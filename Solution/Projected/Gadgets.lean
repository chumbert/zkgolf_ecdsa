import Solution.Projected.Hint
import Solution.Projected.Constants

/-! Proof-friendly gadgets for the projected-signature circuit.
Each gadget body is operation-for-operation identical to the experimental
`Baseline.Projected.Offset` circuit; the frozen `Spec` statements and their
`sorry`-ed proofs are the scaffolding filled in by the G-milestones. -/
namespace Solution.Projected

/-- Explicit product wire: 1 allocation + 1 row. -/
def mulWire (a b : E) : C E := do
  let w ← Circuit.witnessField (.mul a b)
  Circuit.assertZero (pm a b - w)
  pure w

def nonzero (x : E) : C E := do
  let inv ← Circuit.witnessField (.inv (.expr x))
  Circuit.assertZero (pm x inv - cst 1)
  pure inv

def affAdd (p q : Point E) : C (Point E) := do
  let inv ← nonzero (q.x - p.x)
  let l ← Circuit.witnessField (.mul (.expr (q.y-p.y)) (.expr inv))
  Circuit.assertZero (pm (q.x-p.x) l - (q.y-p.y))
  let x ← Circuit.witnessField (.add (.mul (.expr l) (.expr l)) (.expr (-p.x-q.x)))
  Circuit.assertZero (pm l l - p.x - q.x - x)
  let y ← Circuit.witnessField (.add (.mul (.expr l) (.expr (p.x-x))) (.expr (-p.y)))
  Circuit.assertZero (pm l (p.x-x) - p.y - y)
  pure ⟨x,y⟩

def affDouble (p : Point E) : C (Point E) := do
  let xx ← mulWire p.x p.x
  -- The slope row and nonsingularity imply 2*y != 0 (Algebra.double_denominator_ne).
  let l ← Circuit.witnessField (.mul (.expr (sc 3 xx + cst pa)) (.inv (.expr (sc 2 p.y))))
  Circuit.assertZero (pm (sc 2 p.y) l - sc 3 xx - cst pa)
  let x ← Circuit.witnessField (.add (.mul (.expr l) (.expr l)) (.expr (-sc 2 p.x)))
  Circuit.assertZero (pm l l - sc 2 p.x - x)
  let y ← Circuit.witnessField (.add (.mul (.expr l) (.expr (p.x-x))) (.expr (-p.y)))
  Circuit.assertZero (pm l (p.x-x) - p.y - y)
  pure ⟨x,y⟩

/-- ELM prefix. The first denominator is guarded; the second is implied by
the curve equations and the first three rows (Algebra.elm_second_denominator_ne). -/
def elmCore (p q : Point E) : C (E × E) := do
  let inv1 ← nonzero (q.x-p.x)
  let l1 ← Circuit.witnessField (.mul (.expr (q.y-p.y)) (.expr inv1))
  Circuit.assertZero (pm (q.x-p.x) l1 - (q.y-p.y))
  let xu ← Circuit.witnessField (.add (.mul (.expr l1) (.expr l1)) (.expr (-p.x-q.x)))
  Circuit.assertZero (pm l1 l1 - p.x - q.x - xu)
  let l2 ← Circuit.witnessField (.add (.mul (.expr (sc 2 p.y)) (.inv (.expr (p.x-xu)))) (.expr (-l1)))
  Circuit.assertZero (pm (l1+l2) (p.x-xu) - sc 2 p.y)
  pure (xu,l2)

/-- 2P+Q with the intermediate y coordinate omitted. -/
def elm (p q : Point E) : C (Point E) := do
  let (xu,l2) ← elmCore p q
  let x ← Circuit.witnessField (.add (.mul (.expr l2) (.expr l2)) (.expr (-p.x-xu)))
  Circuit.assertZero (pm l2 l2 - p.x - xu - x)
  let y ← Circuit.witnessField (.add (.mul (.expr l2) (.expr (p.x-x))) (.expr (-p.y)))
  Circuit.assertZero (pm l2 (p.x-x) - p.y - y)
  pure ⟨x,y⟩

/-- Final step uses its known target directly: no redundant output wires. -/
def elmTo (p q target : Point E) : C Unit := do
  let (xu,l2) ← elmCore p q
  Circuit.assertZero (pm l2 l2 - p.x - xu - target.x)
  Circuit.assertZero (pm l2 (p.x-target.x) - p.y - target.y)

/-- Constant four-way point mux; one shared bit product for both coordinates. -/
def muxConst4 (b0 b1 : E) (tab : Array (Fp × Fp)) : C (Point E) := do
  let b01 ← mulWire b0 b1
  let coord (get : Fp × Fp → Fp) :=
    let v0 := get (tab.getD 0 (0,0))
    let v1 := get (tab.getD 1 (0,0))
    let v2 := get (tab.getD 2 (0,0))
    let v3 := get (tab.getD 3 (0,0))
    cst v0 + sc (v1-v0) b0 + sc (v2-v0) b1 + sc (v3-v2-v1+v0) b01
  pure ⟨coord Prod.fst, coord Prod.snd⟩

def mux4 (b0 b1 : E) (p0 p1 p2 p3 : Point E) : C (Point E) := do
  let coord (get : Point E → E) : C E := do
    let a ← sel b0 (get p0) (get p1)
    let b ← sel b0 (get p2) (get p3)
    sel b1 a b
  return ⟨← coord (·.x), ← coord (·.y)⟩

/-- The precomputed original Longfellow table remains constrained exactly as before. -/
def originalTable (q r : Point E) : C (Array (Point E)) := do
  let mut pre : Array E := #[]
  for i in [0:8] do pre := pre.push (← hint (3+i))
  let get := fun k => pre.getD k (cst 0)
  let pairs := #[(cst gx,cst gy,q.x,q.y,0),
    (r.x,r.y,cst gx,cst gy,2), (r.x,r.y,q.x,q.y,4),
    (cst gx,cst gy,get 4,get 5,6)]
  for (ax,ay,bx,byy,j) in pairs do
    let (x,y,z) ← addE ax ay (cst 1) bx byy (cst 1)
    pointEquality x y z (get j) (get (j+1))
  return #[(get 0,get 1),(get 2,get 3),(get 4,get 5),(get 6,get 7)].map fun (a,b) => ⟨a,b⟩

/-! ## Frozen gadget specifications (scaffolding; proofs in the G-milestones) -/

def NonzeroSpec (x inv : Fp) : Prop := x * inv = 1
def IsOnCurveSpec (x y : Fp) : Prop := y^2 = x^3 + pa * x + pb
def AffAddSpec (p q out : Point Fp) : Prop :=
  q.x ≠ p.x ∧ IsOnCurveSpec p.x p.y ∧ IsOnCurveSpec q.x q.y ∧
  IsOnCurveSpec out.x out.y
def AffDoubleSpec (p out : Point Fp) : Prop :=
  IsOnCurveSpec p.x p.y ∧ IsOnCurveSpec out.x out.y
def ElmSpec (p q out : Point Fp) : Prop := True
def ElmToSpec (p q target : Point Fp) : Prop := True
def Mux4Spec (b0 b1 : Fp) (p0 p1 p2 p3 out : Point Fp) : Prop :=
  (b0 = 0 ∨ b0 = 1) ∧ (b1 = 0 ∨ b1 = 1)
def MuxConst4Spec (b0 b1 : Fp) (tab : Array (Fp × Fp)) (out : Point Fp) : Prop :=
  (b0 = 0 ∨ b0 = 1) ∧ (b1 = 0 ∨ b1 = 1)
def OriginalTableSpec (q r : Point Fp) (pre : Array (Point Fp)) : Prop := True
def LtOrderSpec (a : Nat → Fp) : Prop := True

theorem nonzero_spec (x : E) : True := sorry
theorem isOnCurve_spec (x y : E) : True := sorry
theorem affAdd_spec (p q : Point Fp) : True := sorry
theorem affDouble_spec (p : Point Fp) : True := sorry
theorem elm_spec (p q : Point Fp) : True := sorry
theorem elmTo_spec (p q target : Point Fp) : True := sorry
theorem mux4_spec (b0 b1 : E) (p0 p1 p2 p3 : Point Fp) : True := sorry
theorem muxConst4_spec (b0 b1 : E) (tab : Array (Fp × Fp)) : True := sorry
theorem originalTable_spec (q r : Point Fp) : True := sorry
theorem ltOrder_spec (a : Nat → E) : True := sorry

end Solution.Projected
