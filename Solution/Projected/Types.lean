import Challenge.Instances.ECDSA_P256_Projected.Interface
import Challenge.Utils.CostR1CS
import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving

/-! Shared types and expression syntax for the projected-signature solution circuit. -/
namespace Solution.Projected

abbrev K := Challenge.Specs.ECDSAP256.K
abbrev Fp := K
abbrev E := Expression Fp
abbrev C := Circuit Fp

/-- Affine point over the circuit field. -/
structure Point (F : Type) where
  x : F
  y : F
  deriving ProvableStruct, Repr, Inhabited

/-- A four-entry table of points (fixed-base window or offset table). -/
abbrev Table4 (F : Type) := Fin 4 → Point F

def deg : E → ℕ := Challenge.CostR1CS.degree
def cst (c : Fp) : E := .const c
def sc (c : Fp) (e : E) : E := .mul (.const c) e
def constVal (e : E) : Fp := e.eval ⟨fun _ => 0, fun _ _ => #[]⟩

/-- Make `e` affine by giving every product term its own wire (1 allocation + 1 row each). -/
def mat : E → C E
  | .var v => pure (.var v)
  | .const c => pure (.const c)
  | .add a b => do
      let a' ← mat a
      let b' ← mat b
      pure (a' + b')
  | .mul a b => do
      let a' ← mat a
      let b' ← mat b
      if deg a' = 0 ∨ deg b' = 0 then pure (.mul a' b')
      else do
        let w ← Circuit.witnessField (.mul (.expr a') (.expr b'))
        Circuit.assertZero (.mul a' b' - w)
        pure w

/-- Product that is allocated immediately. -/
def mm (a b : E) : C E := mat (.mul a b)
/-- Product left pending (free until it is consumed by `mat` or an assertion). -/
def pm (a b : E) : E := .mul a b

/-- Flatten an expression into (coefficient, term) items; a term is a leaf or a product of
two non-constant factors. -/
def flat (c : Fp) : E → List (Fp × E)
  | .add a b => flat c a ++ flat c b
  | .mul a b =>
      if deg a = 0 then flat (c * constVal a) b
      else if deg b = 0 then flat (c * constVal b) a
      else [(c, .mul a b)]
  | e => [(c, e)]

def isProd : E → Bool
  | .mul _ _ => true
  | _ => false

/-- Assert `e = 0`: one product stays in the assertion's own row, the rest get wires. -/
def assertZeroLazy (e : E) : C Unit := do
  let items := flat 1 e
  let prods := items.filter (fun it => isProd it.2)
  let lins := items.filter (fun it => !isProd it.2)
  match prods with
  | [] => Circuit.assertZero e
  | (c, .mul a b) :: rest => do
      let a' ← mat a
      let b' ← mat b
      let mut acc : E := sc c (.mul a' b')
      for (c', t) in rest do
        let w ← mat t
        acc := acc + sc c' w
      for (c', t) in lins do
        acc := acc + sc c' t
      Circuit.assertZero acc
  | _ => pure ()

/-! ## Curve constants -/

def pa : Fp := Challenge.Specs.ECDSAP256.params.a
def pb : Fp := Challenge.Specs.ECDSAP256.params.b
def k3b : Fp := pb + pb + pb
def gx : Fp := Challenge.Specs.ECDSAP256.params.gx
def gy : Fp := Challenge.Specs.ECDSAP256.params.gy

/-! ## Complete addition (verify_circuit.h `addE`) -/

/-- 12 products; the six that feed the outputs are left pending. -/
def addE (X1 Y1 Z1 X2 Y2 Z2 : E) : C (E × E × E) := do
  let t0 ← mm X1 X2
  let t1 ← mm Y1 Y2
  let t2 ← mm Z1 Z2
  let t3p ← mm (X1 + Y1) (X2 + Y2)
  let t3 := t3p - (t0 + t1)
  let t4p ← mm (X1 + Z1) (X2 + Z2)
  let t4 := t4p - (t0 + t2)
  let t5p ← mm (Y1 + Z1) (Y2 + Z2)
  let t5 := t5p - (t1 + t2)
  let Z3a := sc pa t4
  let X3a := sc k3b t2
  let Z3b := X3a + Z3a
  let X3b := t1 - Z3b
  let Z3c := t1 + Z3b
  let Y3p := pm X3b Z3c
  let t1' := sc 3 t0
  let t2a := sc pa t2
  let t4a := sc k3b t4
  let t1b := t1' + t2a
  let t2b := t0 - t2a
  let t2c := sc pa t2b
  let t4b := t4a + t2c
  let m1 := pm t1b t4b
  let Y3 := Y3p + m1
  let m2 := pm t5 t4b
  let X3p := pm t3 X3b
  let X3 := X3p - m2
  let m3 := pm t3 t1b
  let Z3p := pm t5 Z3c
  let Z3 := Z3p + m3
  pure (X3, Y3, Z3)

/-! ## Small gadgets shared with the original circuit -/

def isOnCurve (x y : E) : C Unit := do
  let xx ← mm x x
  assertZeroLazy (.mul y y - (.mul x xx + sc pa x + cst pb))

def pointEquality (x y z px py : E) : C Unit := do
  let z' ← mat z
  assertZeroLazy (x - .mul z' px)
  assertZeroLazy (y - .mul z' py)

def assertBool (b : E) : C Unit := Circuit.assertZero (.mul b b - b)

/-- `x0` if `b = 0`, `x1` if `b = 1`; free when `x1 - x0` is constant. -/
def sel (b x0 x1 : E) : C E := mat (x0 + .mul b (x1 - x0))

/-- Runs of equal bits of the inclusive bound `n-1`, most significant first. -/
def boundRuns : List (Nat × Nat × Bool) := Id.run do
  let nb := fun k => (Challenge.Specs.ECDSAP256.n - 1).testBit k
  let mut out : Array (Nat × Nat × Bool) := #[]
  let mut hi := 255
  for j in [0:256] do
    let k := 255 - j
    if k == 0 || nb (k - 1) != nb k then
      out := out.push (hi, k, nb k)
      hi := k - 1
  return out.toList

/-- Assert `a < n` as `a ≤ n-1`, given boolean affine bits. -/
def assertLtOrder (a : Nat → E) : C Unit := do
  let mut missing : E := cst 0
  for (hi, lo, bit) in boundRuns do
    let len := hi - lo + 1
    if bit then
      for j in [0:len] do
        missing := missing + (cst 1 - a (hi - j))
    else
      let sum := (List.range len).foldl
        (fun s j => s + a (hi - j)) (cst 0)
      let quotient ← Circuit.witnessField (.mul (.expr sum) (.inv (.expr missing)))
      Circuit.assertZero (pm missing quotient - sum)

end Solution.Projected
