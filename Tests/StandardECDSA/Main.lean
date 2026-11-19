/-
# Standard P-256 ECDSA circuit: executable regression suite (T19)

Runs the assembled circuit `StandardECDSA.main` on a fixture set and compares
its verdict against `Tests.StandardECDSA.Oracle`, an *independent* affine
implementation of standard P-256 ECDSA verification that shares no code with
the circuit or with the vendored Longfellow library.

The oracle is the acceptance criterion, **not** the Longfellow accept/reject
labels: the standard-valid inputs that Longfellow's circuit rejects (for
example `Q = -G`, `Q + R = O`, `Q = R`, and `x(R) ≥ n`) must be *accepted*
here.

Coverage:

* valid signatures, including `Q = -G`, `Q + R = O`, `Q = R`;
* the overflow branch `n ≤ x(R) < p` (so `x(R) mod n = r` with `overflow = 1`);
* digest edge values `0, 1, n-1, n, p-1, p, p+1, 2^256-1`, including the pair
  `1` and `p+1` which are distinct digests separated by `p` and therefore have
  distinct limb inputs;
* invalid keys, `r = 0`, `s = 0`, `r, s` out of range, malformed digest limbs,
  altered digest, altered signature, and a signature whose verification point
  is the point at infinity;
* mutations of the seed (digest / `r` / `t` bits, `overflow`, `R.y`, `H`) and of
  computed wires.

Positive fixtures require the honest prover to succeed (the offset search over
the 1,040 candidates of `Math/OffsetCandidates.lean` must find a good `H`).
Negative fixtures are checked over a *sampled* seed space; the exhaustive
statement is the proved theorem `StandardECDSA.main_soundness`.

Run with `lake exe standardEcdsaTests`.

Task T19.
-/
import Tests.StandardECDSA.Oracle
import StandardECDSA.Check

namespace Tests.StandardECDSA.Main

section

open _root_.StandardECDSA
open _root_.StandardECDSA.Math
open StandardECDSA.Gadgets

/-! ## Circuit plumbing

The circuit-side helpers are re-exported under local names so that this module
does not have to `open StandardECDSA.Check`, whose `verifyPoint` would clash with
the oracle's. -/

/-- The circuit's flat operation list. -/
def ops : List (FlatOperation Fp) := _root_.StandardECDSA.Check.operations.toFlat

/-- The circuit's certified cost. -/
def circuitCount : Challenge.CostR1CS.Count := _root_.StandardECDSA.Check.count

/-- The honest-prover offset search. -/
def searchH := _root_.StandardECDSA.Check.searchH

/-- The 772-cell seed layout. -/
def seedOf := _root_.StandardECDSA.Check.seedOf

/-- The flat hint provider. -/
def hintProvider := _root_.StandardECDSA.Check.hintProvider

/-- The first failing assertion for a given seed. -/
def firstFailure := _root_.StandardECDSA.Check.firstFailure

/-- The six circuit inputs, from natural numbers.  The digest is split into
128-bit limbs; `r` and `s` are embedded as field elements. -/
def inputOf (pkx pky E r s : Nat) : Input Fp :=
  { pkX := (pkx : Fp)
    pkY := (pky : Fp)
    digestLo := ((E % 2 ^ 128 : Nat) : Fp)
    digestHi := ((E / 2 ^ 128 : Nat) : Fp)
    r := (r : Fp)
    s := (s : Fp) }

/-- The `k`-th offset candidate `H = [k]G`, in affine coordinates. -/
def offsetPoint (k : Nat) : Fp × Fp :=
  let h := (List.range (k - 1)).foldl
    (fun h _ => _root_.addE h FixedTables.gPoint Challenge.Specs.ECDSAP256.params)
    FixedTables.gPoint
  FixedTables.affine h

/-- The honest 772-cell seed for the verification point `V = (vx, vy)` and
offset candidate `H = [k]G`. -/
def honestSeed (vx vy : Nat) (E r s k : Nat) : Array Fp :=
  let overflow : Fp := if vx < n then 0 else 1
  let (hx, hy) := offsetPoint k
  seedOf (vy : Fp) hx hy overflow E r (n - s)

/-- Does the circuit accept with the honest seed for some offset candidate
`H = [k]G`, `1 ≤ k ≤ 1040`? -/
def acceptsHonest (inp : Input Fp) (vx vy : Nat) (E r s : Nat) : Option Nat :=
  let overflow : Fp := if vx < n then 0 else 1
  searchH ops inp (vy : Fp) overflow E r (n - s) 1040

/-- Does the circuit accept for any seed in a small sampled seed space
(`R.y ∈ {0,1,2,3}`, `overflow ∈ {0,1}`, `H ∈ {[1]G, [2]G, [3]G}`)? -/
def acceptsSampled (inp : Input Fp) (E r s : Nat) : Bool :=
  [0, 1, 2, 3].any fun ry =>
    [0, 1].any fun ov =>
      (searchH ops inp (ry : Fp) (ov : Fp) E r (n - s) 3).isSome

/-- The witness array produced by the circuit's witness generation. -/
def witnessOf (inp : Input Fp) (seed : Array Fp) : Array Fp :=
  FlatOperation.witgen (hintProvider seed) ops (toElements inp).toArray

/-- The index of the first failing assertion for a given witness array. -/
def firstFailureOf (wires : Array Fp) : Option Nat := Id.run do
  let env : Environment Fp := Environment.fromArray wires (fun _ _ => #[])
  let mut row := 0
  for op in ops do
    match op with
    | .assert e =>
        if e.eval env != 0 then return some row
        row := row + 1
    | _ => pure ()
  return none

/-- Flip the `i`-th seed cell between `0` and `1`. -/
def flipSeedBit (seed : Array Fp) (i : Nat) : Array Fp :=
  seed.set! i (if seed.getD i 0 == 0 then 1 else 0)

/-! ## Fixture construction -/

/-- The baseline digest. -/
def digest0 : Nat := 0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef

/-- The overflow fixture: `n ≤ x(R) < p`, so `x(R) mod n = r` with
`overflow = 1`.  `Q = [r⁻¹]([s]R - [E]G)` makes the verification point `R`. -/
def overflowFixture : Option (Nat × Nat × Nat × Nat × Nat) := do
  let (x, y) ← Oracle.findOverflowX 1000
  let r := x - n
  if r == 0 then none else
  let E := digest0
  let s := 7
  let R : Oracle.APt := some ((x : ZMod p), y)
  let Q := Oracle.mulA (Oracle.invN r) (Oracle.subA (Oracle.mulA s R) (Oracle.mulA (E % n) Oracle.gA))
  let (qx, qy) ← Q
  some (qx.val, qy.val, E, r, s)

/-- The infinity fixture: `Q = -[E·r⁻¹]G` makes the verification point `O`. -/
def infinityFixture : Option (Nat × Nat × Nat × Nat × Nat) := do
  let E := digest0
  let r := 12345
  let s := 67890
  let Q ← Oracle.negA (Oracle.mulA (E % n * Oracle.invN r % n) Oracle.gA)
  some (Q.1.val, Q.2.val, E, r, s)

/-! ## Reporting -/

/-- Pass/fail counters. -/
structure Ctx where
  passed : IO.Ref Nat
  failed : IO.Ref Nat

/-- Record one check. -/
def Ctx.check (c : Ctx) (name : String) (ok : Bool) (detail : String) : IO Unit := do
  if ok then
    c.passed.modify (· + 1)
    IO.println s!"  PASS  {name}  {detail}"
  else
    c.failed.modify (· + 1)
    IO.println s!"  FAIL  {name}  {detail}"

/-! ## Fixture runners -/

/-- A positive fixture: the oracle accepts and the circuit's honest prover
succeeds. -/
def positive (c : Ctx) (name : String) (pkx pky E r s : Nat) : IO Unit := do
  let inp := inputOf pkx pky E r s
  let oracle := Oracle.verify pkx pky E r s
  match Oracle.verifyPoint pkx pky E r s with
  | none =>
      c.check name false s!"oracle={oracle} but V = O, so there is no honest seed"
  | some (vx, vy) =>
      let circuit := acceptsHonest inp vx.val vy.val E r s
      c.check name (oracle && circuit.isSome)
        s!"oracle={oracle} circuit={circuit} (H = [{circuit.getD 0}]G)"

/-- A negative fixture: the oracle rejects and the circuit rejects for every
seed in the sampled seed space. -/
def negative (c : Ctx) (name : String) (pkx pky E r s : Nat) : IO Unit := do
  let inp := inputOf pkx pky E r s
  let oracle := Oracle.verify pkx pky E r s
  let circuit := acceptsSampled inp E r s
  c.check name (!oracle && !circuit)
    s!"oracle={oracle} circuit-accepts-sampled-seed={circuit}"

/-- A circuit-only rejection fixture (the oracle has no notion of the limb
encoding, so only the circuit's verdict is checked). -/
def circuitRejects (c : Ctx) (name : String) (inp : Input Fp) (E r s : Nat) : IO Unit := do
  let circuit := acceptsSampled inp E r s
  c.check name (!circuit) s!"circuit-accepts-sampled-seed={circuit}"

/-! ## The suite -/

/-- Valid signatures, including the standard-valid exceptions. -/
def positiveFixtures (c : Ctx) : IO Unit := do
  IO.println "positive fixtures (oracle accepts, circuit's honest prover succeeds)"
  let k0 := 67890
  let cases : List (String × Nat × Nat) :=
    [ ("valid-baseline", 12345, k0)
    , ("valid-Q-eq-negG", n - 1, k0)
    , ("valid-Q-plus-R-eq-O", n - k0, k0)
    , ("valid-Q-eq-R", k0, k0)
    , ("valid-small-key", 1, k0)
    , ("valid-key-n-minus-2", n - 2, k0) ]
  for (name, d, k) in cases do
    match Oracle.signWith d k digest0 with
    | none => c.check name false "fixture construction failed"
    | some (qx, qy, r, s) => positive c name qx qy digest0 r s
  let digests : List (String × Nat) :=
    [ ("valid-digest-0", 0)
    , ("valid-digest-1", 1)
    , ("valid-digest-n-minus-1", n - 1)
    , ("valid-digest-n", n)
    , ("valid-digest-p-minus-1", p - 1)
    , ("valid-digest-p", p)
    , ("valid-digest-p-plus-1", p + 1)
    , ("valid-digest-2-pow-256-minus-1", 2 ^ 256 - 1) ]
  for (name, E) in digests do
    match Oracle.signWith 12345 k0 E with
    | none => c.check name false "fixture construction failed"
    | some (qx, qy, r, s) => positive c name qx qy E r s
  match overflowFixture with
  | none => c.check "valid-overflow" false "no x ≥ n on the curve found"
  | some (qx, qy, E, r, s) =>
      let inp := inputOf qx qy E r s
      let oracle := Oracle.verify qx qy E r s
      match Oracle.verifyPoint qx qy E r s with
      | none => c.check "valid-overflow" false "V = O"
      | some (vx, vy) =>
          let circuit := acceptsHonest inp vx.val vy.val E r s
          c.check "valid-overflow" (oracle && circuit.isSome)
            s!"x(V) = n + {vx.val - n} (overflow = 1) oracle={oracle} circuit={circuit}"

/-- Invalid inputs: the oracle rejects and the circuit rejects. -/
def negativeFixtures (c : Ctx) : IO Unit := do
  IO.println "negative fixtures (oracle rejects, circuit rejects on sampled seeds)"
  let some (qx, qy, r, s) := Oracle.signWith 12345 67890 digest0
    | c.check "negative-setup" false "fixture construction failed"; return
  let E := digest0
  negative c "invalid-r-zero" qx qy E 0 s
  negative c "invalid-s-zero" qx qy E r 0
  negative c "invalid-r-eq-n" qx qy E n s
  negative c "invalid-s-eq-n" qx qy E r n
  negative c "invalid-r-gt-n" qx qy E (n + 1) s
  negative c "invalid-s-gt-n" qx qy E r (n + 1)
  negative c "invalid-pk-off-curve" qx (qy + 1) E r s
  negative c "invalid-altered-digest" qx qy (E + 1) r s
  negative c "invalid-altered-signature" qx qy E (r + 1) s
  match infinityFixture with
  | none => c.check "invalid-V-infinity" false "fixture construction failed"
  | some (ix, iy, iE, ir, is) => negative c "invalid-V-infinity" ix iy iE ir is
  let badLo : Input Fp :=
    { inputOf qx qy E r s with digestLo := ((2 ^ 128 : Nat) : Fp) }
  circuitRejects c "invalid-digest-lo-limb" badLo E r s
  let badHi : Input Fp :=
    { inputOf qx qy E r s with digestHi := ((2 ^ 128 : Nat) : Fp) }
  circuitRejects c "invalid-digest-hi-limb" badHi E r s

/-- Seed and computed-wire mutations of the baseline fixture. -/
def mutationFixtures (c : Ctx) : IO Unit := do
  IO.println "mutation fixtures (honest witness must break)"
  let some (qx, qy, r, s) := Oracle.signWith 12345 67890 digest0
    | c.check "mutation-setup" false "fixture construction failed"; return
  let E := digest0
  let inp := inputOf qx qy E r s
  let some (vx, vy) := Oracle.verifyPoint qx qy E r s
    | c.check "mutation-setup" false "V = O"; return
  let seed := honestSeed vx.val vy.val E r s 1
  c.check "mutation-baseline-honest-seed" ((firstFailure ops inp seed).isNone)
    s!"first failure = {firstFailure ops inp seed}"
  -- seed layout: [R.y, H.x, H.y, overflow, then (E_i, r_i, t_i) for i < 256]
  for (name, cell) in
      [ ("mutation-seed-digest-bit", 4 + 3 * 7)
      , ("mutation-seed-r-bit", 5 + 3 * 7)
      , ("mutation-seed-t-bit", 6 + 3 * 7)
      , ("mutation-seed-digest-msb", 4 + 3 * 255)
      , ("mutation-seed-r-msb", 5 + 3 * 255)
      , ("mutation-seed-t-msb", 6 + 3 * 255)
      , ("mutation-seed-overflow", 3)
      , ("mutation-seed-Ry", 0)
      , ("mutation-seed-Hx", 1)
      , ("mutation-seed-Hy", 2) ] do
    let fail := firstFailure ops inp (flipSeedBit seed cell)
    c.check name fail.isSome s!"first failure = {fail}"
  let wires := witnessOf inp seed
  c.check "mutation-witness-size" (wires.size == 4634) s!"wires = {wires.size}"
  for w in [6, 100, 1000, 2000, 3000, 4000, 4633] do
    let mutated := wires.set! w (wires.getD w 0 + 1)
    let fail := firstFailureOf mutated
    c.check s!"mutation-computed-wire-{w}" fail.isSome s!"first failure = {fail}"

/-- An `x = 0` public key exists on P-256 (`y² = b` has a solution), so the
plan's "certify existence or impossibility" obligation is discharged by
`xZeroY_sq`.  A *signature* under it is not constructible without a discrete
logarithm, so no positive fixture is included; the circuit's handling of
`x = 0` is covered by the unconditional theorem `main_soundness`. -/
def xZeroY : ZMod p :=
  46263761741508638697010950048709651021688891777877937875096931459006746039284

theorem xZeroY_sq : xZeroY * xZeroY = Challenge.Specs.ECDSAP256.params.b := by decide

theorem xZeroY_onCurve : Oracle.onCurve 0 xZeroY = true := by decide

/-- Run the whole suite. -/
def run : IO UInt32 := do
  IO.println "Standard P-256 ECDSA circuit: regression suite (T19)"
  IO.println s!"circuit: allocations={circuitCount.allocations} rows={circuitCount.constraints} \
score={circuitCount.allocations + circuitCount.constraints}"
  IO.println "oracle: independent affine P-256 verifier (Tests.StandardECDSA.Oracle)"
  IO.println s!"x = 0 public key exists: y² = b has the solution {xZeroY.val}"
  let c : Ctx := { passed := ← IO.mkRef 0, failed := ← IO.mkRef 0 }
  positiveFixtures c
  negativeFixtures c
  mutationFixtures c
  let passed ← c.passed.get
  let failed ← c.failed.get
  IO.println s!"regressions: {passed} passed, {failed} failed"
  return if failed == 0 then 0 else 1

end

end Tests.StandardECDSA.Main

def main (args : List String) : IO UInt32 := Tests.StandardECDSA.Main.run
