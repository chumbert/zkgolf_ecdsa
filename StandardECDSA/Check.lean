/-
# Executable diagnostics for the standard P-256 ECDSA circuit

`lake exe standardEcdsaCheck --count-only` reports the exact allocation and row
count of the assembled circuit, so that it can be compared against the plan's
proposed budget of 4,628 allocations + 4,634 rows = 9,262.

Without `--count-only` the executable additionally runs a *generated-witness*
smoke test: it constructs a standard-valid P-256 ECDSA signature, computes the
honest seed (signature point `R`, offset point `H`, `overflow`, and the 768
scalar bits), evaluates the circuit's witness generation and checks that every
R1CS assertion holds.  This is a diagnostic, not a proof; the proofs are
milestones M3–M5.

Task T18/T19 will extend this executable with the full standard-ECDSA
regression suite and the matrix export.
-/

import StandardECDSA.Main
import Challenge.Utils.CostR1CS
import ECDSA.EC
import Clean.Circuit.WitnessGeneration

namespace StandardECDSA.Check

open Challenge.CostR1CS
open StandardECDSA.Gadgets

/-- The six external inputs, laid out from wire offset `0`. -/
def inputVar : Var Input Fp := varFromOffset Input 0

/-- Build the circuit's operation list. -/
def operations : Operations Fp := Circuit.operations (StandardECDSA.main inputVar) 6

/-- The exact cost of the assembled circuit. -/
def count : Count := operationCount operations

/-! ## Generated-witness smoke test -/

/-- A hint provider backed by a flat array of seed cells (one column). -/
def hintProvider (a : Array Fp) : ProverHint Fp :=
  fun _ n => a.map fun v => Vector.ofFn fun (_ : Fin n) => v

/-- The standard verification point `V = [u₁]G + [u₂]Q`, in affine coordinates. -/
def verifyPoint (pkX pkY : Fp) (E r s : Nat) : Option (Fp × Fp) :=
  let w := invModN s
  let u1 := (E * w) % n
  let u2 := (r * w) % n
  let V := addE (mulG u1) (mulP u2 ⟨pkX, pkY, 1⟩) params
  if V.Z = 0 then none
  else some (V.X * V.Z⁻¹, V.Y * V.Z⁻¹)

/-- The 772-cell seed: `R.y`, `H`, `overflow`, then the 768 scalar bits. -/
def seedOf (ry hx hy overflow : Fp) (E r t : Nat) : Array Fp := Id.run do
  let mut a : Array Fp := #[ry, hx, hy, overflow]
  for i in [0:256] do
    a := a.push (if E.testBit i then 1 else 0)
    a := a.push (if r.testBit i then 1 else 0)
    a := a.push (if t.testBit i then 1 else 0)
  return a

/-- Evaluate the circuit's witness generation on `seed` and return the index of
the first failing assertion, if any. -/
def firstFailure (ops : List (FlatOperation Fp)) (inp : Input Fp) (seed : Array Fp) :
    Option Nat := Id.run do
  let init := (toElements inp).toArray
  let wires := FlatOperation.witgen (hintProvider seed) ops init
  let env : Environment Fp := Environment.fromArray wires (fun _ _ => #[])
  let mut row := 0
  for op in ops do
    match op with
    | .assert e =>
        if e.eval env != 0 then return some row
        row := row + 1
    | _ => pure ()
  return none

/-- Search the first offset candidate `H = [k]G`, `1 ≤ k ≤ maxH`, that makes every
assertion hold. -/
def searchH (ops : List (FlatOperation Fp)) (inp : Input Fp) (ry overflow : Fp)
    (E r t : Nat) (maxH : Nat) : Option Nat := Id.run do
  let mut h := Math.FixedTables.gPoint
  for i in [1:maxH + 1] do
    let (hx, hy) := Math.FixedTables.affine h
    if (firstFailure ops inp (seedOf ry hx hy overflow E r t)).isNone then return some i
    h := _root_.addE h Math.FixedTables.gPoint Challenge.Specs.ECDSAP256.params
  return none

/-- A standard-valid test signature: `Q = [d]G`, `R = [k]G`, `r = x(R) mod n`,
`s = k⁻¹(E + r·d) mod n`. -/
def testVector : Option (Input Fp × Fp × Fp × Nat × Nat) := do
  let d := 12345
  let k := 67890
  let E := 0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef
  let Q := mulG d
  let pkX := Q.X * Q.Z⁻¹
  let pkY := Q.Y * Q.Z⁻¹
  let R := mulG k
  let rxNat := (R.X * R.Z⁻¹).val
  let r := rxNat % n
  if r == 0 then none
  let s := (invModN k * ((E + r * d) % n)) % n
  if s == 0 then none
  let some (vx, vy) := verifyPoint pkX pkY E r s | none
  let vxNat := vx.val
  let overflow : Fp := if vxNat = r then 0 else if vxNat = r + n then 1 else 999
  let inp : Input Fp := {
    pkX := pkX, pkY := pkY,
    digestLo := ((E % 2 ^ 128 : Nat) : Fp), digestHi := ((E / 2 ^ 128 : Nat) : Fp),
    r := (r : Fp), s := (s : Fp) }
  return (inp, vy, overflow, E, r)

/-! ## Standalone check of the gated comparator (plan §3B)

Simulates the rows of `assertLtOrderOf` / `assertLtOrderGuardedOf` on a concrete
bit vector, using exactly the witness the circuit's `witgen` computes
(`quotient = sum * factor⁻¹`).  This validates the plan's construction
independently of the rest of the circuit. -/

/-- Simulate the comparator rows.  `guard = none` is the ordinary comparator. -/
def comparatorOk (bound : Nat) (guard : Option Bool) (a : Nat → Bool) : Bool := Id.run do
  let mut missing : Fp := 0
  let mut ok := true
  for (hi, lo, bit) in boundRunsOf bound do
    let len := hi - lo + 1
    if bit then
      for j in [0:len] do
        missing := missing + (1 - (if a (hi - j) then 1 else 0))
    else
      let sum : Fp := (List.range len).foldl
        (fun s j => s + (if a (hi - j) then 1 else 0)) 0
      let factor : Fp := match guard with
        | none => missing
        | some g => missing + (1 - (if g then 1 else 0))
      let q := sum * factor⁻¹
      if factor * q != sum then ok := false
  return ok

/-- `a ≤ bound` as a natural number. -/
def leOfBits (a : Nat → Bool) (bound : Nat) : Bool :=
  (List.range 256).foldl (fun acc i => acc || (a i && !bound.testBit i)) false

def comparatorReport : IO UInt32 := do
  let mut bad := 0
  let mut checked := 0
  -- ordinary comparator: sound and complete for `a ≤ n-1`
  for v in [0, 1, 2, n - 2, n - 1, n, n + 1, 2 ^ 256 - 1] do
    let a : Nat → Bool := fun i => v.testBit i
    let ok := comparatorOk nSubOne none a
    let want := decide (v ≤ n - 1)
    checked := checked + 1
    if ok != want then
      bad := bad + 1
      IO.println s!"  comparator MISMATCH at v={v}: rows={repr ok} expected={repr want}"
  -- guarded comparator, guard = 1: same as the ordinary one
  for v in [0, 1, n - 2, n - 1, n, 2 ^ 256 - 1] do
    let a : Nat → Bool := fun i => v.testBit i
    let ok := comparatorOk pSubNSubOne (some true) a
    let want := decide (v ≤ pSubNSubOne)
    checked := checked + 1
    if ok != want then
      bad := bad + 1
      IO.println s!"  guarded(1) MISMATCH at v={v}: rows={repr ok} expected={repr want}"
  -- guarded comparator, guard = 0: always satisfiable
  for v in [0, 1, pSubNSubOne, pSubNSubOne + 1, n - 1, 2 ^ 256 - 1] do
    let a : Nat → Bool := fun i => v.testBit i
    let ok := comparatorOk pSubNSubOne (some false) a
    checked := checked + 1
    if !ok then
      bad := bad + 1
      IO.println s!"  guarded(0) UNSATISFIABLE at v={v}"
  IO.println s!"comparator: {checked} cases, {bad} failures"
  return if bad == 0 then 0 else 1


/-! ## Matrix export (T20)

`--export <dir>` writes the circuit's R1CS rows and a satisfying witness so that
`scripts/check_standard_ecdsa_matrices.py` can validate them independently of
Lean.  Each assertion is decomposed into `A * B - C` with `A`, `B`, `C` sparse
affine forms; the exporter refuses to write a row it cannot decompose.
-/

/-- A sparse affine form: variable coefficients and a constant term. -/
abbrev LF := List (Nat × Fp) × Fp

/-- Evaluate a sparse affine form on a witness vector. -/
def LF.eval (z : Array Fp) (f : LF) : Fp :=
  f.1.foldl (fun acc p => acc + p.2 * z.getD p.1 0) f.2

/-- Decompose an affine expression into a sparse form. -/
def linForm : E → Option LF
  | .var v => some ([(v.index, 1)], 0)
  | .const c => some ([], c)
  | .add a b => do
      let fa ← linForm a
      let fb ← linForm b
      pure (fa.1 ++ fb.1, fa.2 + fb.2)
  | .mul a b => do
      let fa ← linForm a
      let fb ← linForm b
      if fa.1.isEmpty then pure (fb.1.map fun p => (p.1, fa.2 * p.2), fa.2 * fb.2)
      else if fb.1.isEmpty then pure (fa.1.map fun p => (p.1, p.2 * fb.2), fa.2 * fb.2)
      else failure

/-- Scale a sparse affine form by a constant. -/
def LF.scale (c : Fp) (f : LF) : LF := (f.1.map fun p => (p.1, c * p.2), c * f.2)

/-- Decompose an assertion into `A * B - C`, looking through constant scalars. -/
def r1csOf : E → Option (LF × LF × LF)
  | .add a b =>
      match r1csOf a, r1csOf b with
      | some _, some _ => none
      | some (A, B, C), none =>
          (linForm b).map fun fb =>
            (A, B, (C.1 ++ fb.1.map fun p => (p.1, -p.2)), C.2 - fb.2)
      | none, some (A, B, C) =>
          (linForm a).map fun fa =>
            (A, B, (C.1 ++ fa.1.map fun p => (p.1, -p.2)), C.2 - fa.2)
      | none, none => none
  | .mul a b =>
      match linForm a, linForm b with
      | some fa, some fb =>
          if fa.1.isEmpty ∨ fb.1.isEmpty then none else some (fa, fb, ([], 0))
      | some fa, none =>
          if fa.1.isEmpty then
            (r1csOf b).map fun r => (LF.scale fa.2 r.1, r.2.1, LF.scale fa.2 r.2.2)
          else none
      | none, some fb =>
          if fb.1.isEmpty then
            (r1csOf a).map fun r => (LF.scale fb.2 r.1, r.2.1, LF.scale fb.2 r.2.2)
          else none
      | none, none => none
  | _ => none

/-- The R1CS row of an assertion: `A * B - C = 0`, falling back to `0 * 0 - (-e)`
for a purely affine assertion. -/
def rowOf (e : E) : Option (LF × LF × LF) :=
  match r1csOf e with
  | some r => some r
  | none => (linForm e).map fun f =>
      (([], 0), ([], 0), (f.1.map fun p => (p.1, -p.2), -f.2))

def renderLF (f : LF) : String :=
  let terms := f.1.map fun p => s!"{p.1}:{p.2.val}"
  s!"{String.intercalate "," terms}|{f.2.val}"

/-- Export the matrices and a satisfying witness. -/
def exportMatrices (dir : System.FilePath) (ops : List (FlatOperation Fp))
    (inp : Input Fp) (seed : Array Fp) : IO UInt32 := do
  let init := (toElements inp).toArray
  let wires := FlatOperation.witgen (hintProvider seed) ops init
  let mut rows : Array String := #[]
  let mut bad := 0
  for op in ops do
    match op with
    | .assert e =>
        match rowOf e with
        | some (A, B, C) => rows := rows.push s!"{renderLF A};{renderLF B};{renderLF C}"
        | none =>
            bad := bad + 1
            IO.println s!"export: undecomposable row {rows.size + bad}: {repr e}"
    | _ => pure ()
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "rows.txt") (String.intercalate "\n" rows.toList ++ "\n")
  IO.FS.writeFile (dir / "witness.txt")
    (String.intercalate "\n" (wires.toList.map fun v => toString v.val) ++ "\n")
  IO.FS.writeFile (dir / "meta.txt")
    (s!"inputs=6\nallocations={count.allocations}\nrows={count.constraints}\n" ++
     s!"exported_rows={rows.size}\nundecomposable={bad}\n" ++
     s!"input_values={String.intercalate "," ((toElements inp).toList.map fun v => toString v.val)}\n")
  IO.println s!"export: {rows.size} rows, {wires.size} wires, {bad} undecomposable -> {dir}"
  return if bad == 0 then 0 else 1

def run (args : List String) : IO UInt32 := do
  IO.println "Standard P-256 ECDSA circuit (6 fixed inputs)"
  IO.println s!"allocations={count.allocations} rows={count.constraints} score={count.allocations + count.constraints}"
  if args.contains "--count-only" then return 0
  if args.contains "--comparator" then return ← comparatorReport
  if let some dir := args.findSome? (fun a => (a.dropPrefix? "--export=").map (fun s => System.FilePath.mk s.toString)) then
    let ops := operations.toFlat
    let some (inp, ry, overflow, E, r) := testVector
      | IO.println "export: failed to build the test vector"; return 1
    let t := n - inp.s.val
    let some k := searchH ops inp ry overflow E r t 1294
      | IO.println "export: no good offset found"; return 1
    let mut h := Math.FixedTables.gPoint
    for _ in [1:k] do
      h := _root_.addE h Math.FixedTables.gPoint Challenge.Specs.ECDSAP256.params
    let (hx, hy) := Math.FixedTables.affine h
    return ← exportMatrices dir ops inp (seedOf ry hx hy overflow E r t)
  let ops := operations.toFlat
  let some (inp, ry, overflow, E, r) := testVector
    | IO.println "smoke test: failed to build the test vector"; return 1
  let t := n - inp.s.val
  IO.println s!"smoke test: r={r} s={inp.s.val} t={t} overflow={overflow.val}"
  if args.contains "--debug" then
    let mut h := Math.FixedTables.gPoint
    for i in [1:9] do
      let (hx, hy) := Math.FixedTables.affine h
      IO.println s!"  H=[{i}]G first failure = {firstFailure ops inp (seedOf ry hx hy overflow E r t)}"
      h := _root_.addE h Math.FixedTables.gPoint Challenge.Specs.ECDSAP256.params
  match searchH ops inp ry overflow E r t 1294 with
  | some k =>
      IO.println s!"smoke test: all R1CS assertions hold with H = [{k}]G"
      return 0
  | none =>
      let (gx0, gy0) := Math.FixedTables.affine Math.FixedTables.gPoint
      let fail := firstFailure ops inp (seedOf ry gx0 gy0 overflow E r t)
      IO.println s!"smoke test: FAILED (first failing row with H = G: {fail})"
      return 1

end StandardECDSA.Check
