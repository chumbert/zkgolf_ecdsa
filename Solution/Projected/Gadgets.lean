import Solution.Projected.Types
import Solution.Projected.Constants
import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Utils.Tactics
import Challenge.Specs.ECDSAP256

/-!
# Gadgets for the proof-friendly projected ECDSA circuit (plan T0.2, part b)

Each gadget is a Clean `FormalCircuit`, `GeneralFormalCircuit` or `FormalAssertion` with a
factored `main`, an explicit `ElaboratedCircuit` instance, a semantic `Spec`, and separate
`<g>_soundness` / `<g>_completeness` theorems. Constraints and costs follow the existing
circuit wire for wire (`Baseline/Circuit.lean`, `Baseline/Optimized.lean`,
`Baseline/Projected/Offset.lean`), with the recursive `mat` replaced by `mulWire`.

Checklist (gadget | Spec | soundness / completeness | alloc/rows | G-task):
* `mulWire`     | out = a*b                                | proved / proved | 1/1 | G1
* `nonzero`     | x ≠ 0 ∧ x*out = 1 (prover assumes x ≠ 0)  | proved / proved | 1/1 | G1
* `assertBool`  | IsBool b                                 | proved / proved | 0/1 | G2
* `bit3 i`      | the hint bits (e_i, r_i, t_i) are boolean | proved / proved | 3/3 | G2
* `isOnCurve`   | y^2 = x^3 + a x + b                      | proved / proved | 2/3 | G3
* `sel`         | out = x0 + b (x1 - x0)                   | proved / proved | 1/1 | G6
* `mux4`        | bits boolean ⇒ out = table.select b0 b1  | proved / proved | 6/6 | G6
* `muxConst4 i` | bits boolean ⇒ out = (constTable i).select b0 b1 | proved / proved | 1/1 | G6
* `affAdd`, `affDouble`, `elm`, `elmTo`: not yet defined (S6)
* `originalTable`, `ltOrder`: not yet defined (S7)
-/

namespace Solution.Projected.Gadgets

open Solution.Projected

/-- P-256 curve coefficients. -/
abbrev curveA : Fp := Challenge.Specs.ECDSAP256.params.a
abbrev curveB : Fp := Challenge.Specs.ECDSAP256.params.b

/-- Selection among four points by two bits, index `b0 + 2*b1`
(matches `Offset.mux4` and the `muxConst4` coefficient formula). -/
def _root_.Solution.Projected.Table4.select {F : Type} [Zero F] [DecidableEq F] (t : Table4 F) (b0 b1 : F) : Point F :=
  if b1 = 0 then (if b0 = 0 then t.p0 else t.p1) else (if b0 = 0 then t.p2 else t.p3)

/-- The constant fixed-base table `i` as points. -/
def constTable (i : Fin 128) : Table4 Fp :=
  ⟨⟨tableX i 0, tableY i 0⟩, ⟨tableX i 1, tableY i 1⟩,
   ⟨tableX i 2, tableY i 2⟩, ⟨tableX i 3, tableY i 3⟩⟩

/-! ## mulWire: one product wire (replaces the recursive `mat`) -/

structure MulWireInput (F : Type) where
  a : F
  b : F
  deriving ProvableStruct

def mulWire_main (input : Var MulWireInput Fp) : Circuit Fp (Var field Fp) := do
  let w ← witnessField (input.a * input.b)
  assertZero (input.a * input.b - w)
  return w

@[reducible] instance mulWire_elaborated :
    ElaboratedCircuit Fp MulWireInput field mulWire_main := by elaborate_circuit

def mulWire_Spec (input : MulWireInput Fp) (out : Fp) : Prop := out = input.a * input.b

theorem mulWire_soundness :
    Soundness Fp mulWire_main (fun _ => True) mulWire_Spec := by
  circuit_proof_start [mulWire_main, mulWire_Spec]
  rcases h_input with ⟨rfl, rfl⟩
  rw [sub_eq_zero] at h_holds
  exact h_holds.symm

theorem mulWire_completeness :
    Completeness Fp mulWire_main (fun _ => True) := by
  circuit_proof_start [mulWire_main]
  rcases h_input with ⟨rfl, rfl⟩
  simp_all

def mulWire : FormalCircuit Fp MulWireInput field where
  main := mulWire_main
  elaborated := mulWire_elaborated
  Spec := mulWire_Spec
  soundness := mulWire_soundness
  completeness := mulWire_completeness

/-! ## nonzero: inverse wire, `x * inv = 1` (as `Offset.nonzero`) -/

def nonzero_main (x : Var field Fp) : Circuit Fp (Var field Fp) := do
  let x : Expression Fp := x
  let inv ← witnessField (Witgen.FExpr.expr x)⁻¹
  assertZero (x * inv - 1)
  return inv

@[reducible] instance nonzero_elaborated :
    ElaboratedCircuit Fp field field nonzero_main := by elaborate_circuit

def nonzero_Spec (x : Fp) (inv : Fp) (_ : ProverData Fp) : Prop := x ≠ 0 ∧ x * inv = 1

def nonzero_ProverAssumptions (x : Fp) (_ : ProverData Fp) (_ : ProverHint Fp) : Prop := x ≠ 0

theorem nonzero_soundness :
    GeneralFormalCircuit.Soundness Fp nonzero_main (fun _ _ => True) nonzero_Spec := by
  circuit_proof_start [nonzero_main, nonzero_Spec]
  subst h_input
  rw [sub_eq_zero] at h_holds
  exact ⟨left_ne_zero_of_mul_eq_one h_holds, h_holds⟩

theorem nonzero_completeness :
    GeneralFormalCircuit.Completeness Fp nonzero_main nonzero_ProverAssumptions
      (fun _ _ _ => True) := by
  circuit_proof_start [nonzero_main, nonzero_ProverAssumptions]
  subst h_input
  simp_all [mul_inv_cancel₀]

def nonzero : GeneralFormalCircuit Fp field field where
  main := nonzero_main
  elaborated := nonzero_elaborated
  Spec := nonzero_Spec
  ProverAssumptions := nonzero_ProverAssumptions
  soundness := nonzero_soundness
  completeness := nonzero_completeness

/-! ## assertBool: `b*b - b = 0` (as `Optimized.assertBool`) -/

def assertBool_main (b : Var field Fp) : Circuit Fp Unit := do
  let b : Expression Fp := b
  assertZero (b * b - b)

@[reducible] instance assertBool_elaborated :
    ElaboratedCircuit Fp field unit assertBool_main := by elaborate_circuit

def assertBool_Spec (b : Fp) : Prop := IsBool b

theorem assertBool_soundness :
    FormalAssertion.Soundness Fp assertBool_main (fun _ => True) assertBool_Spec := by
  circuit_proof_start [assertBool_main, assertBool_Spec]
  subst h_input
  rw [IsBool.iff_mul_sub_one, mul_sub, mul_one]
  exact h_holds

theorem assertBool_completeness :
    FormalAssertion.Completeness Fp assertBool_main (fun _ => True) assertBool_Spec := by
  circuit_proof_start [assertBool_main, assertBool_Spec]
  subst h_input
  rw [IsBool.iff_mul_sub_one, mul_sub, mul_one] at h_spec
  exact h_spec

def assertBool : FormalAssertion Fp field where
  main := assertBool_main
  elaborated := assertBool_elaborated
  Spec := assertBool_Spec
  soundness := assertBool_soundness
  completeness := assertBool_completeness

/-! ## bit3: the three hint bits of weight `2^i` (rows `11+3i`, `12+3i`, `13+3i`) -/

/-- Hint wire `k` exactly as `Offset.hint k`. -/
def hintExpr (k : ℕ) : Witgen.FExpr Fp :=
  .hintGet "offset" 1 (.const k.toUInt64) ⟨0, by decide⟩

/-- Value of hint row `k`, as `hintExpr k` evaluates it. -/
def hintVal (h : ProverHint Fp) (k : ℕ) : Fp :=
  ((h "offset" 1)[(k.toUInt64).toNat]?.getD default)[0]

/-- The digest, `r` and `t = n - s` bits of weight `2^i`. -/
structure Bit3 (F : Type) where
  e : F
  r : F
  t : F
  deriving ProvableStruct

def bit3_main (i : ℕ) (_ : Var unit Fp) : Circuit Fp (Var Bit3 Fp) := do
  let e ← witnessField (hintExpr (11 + 3 * i))
  let r ← witnessField (hintExpr (12 + 3 * i))
  let t ← witnessField (hintExpr (13 + 3 * i))
  Solution.Projected.Gadgets.assertBool e
  Solution.Projected.Gadgets.assertBool r
  Solution.Projected.Gadgets.assertBool t
  return { e, r, t }

@[reducible] instance bit3_elaborated (i : ℕ) :
    ElaboratedCircuit Fp unit Bit3 (bit3_main i) := by elaborate_circuit

def bit3_Spec (_ : Unit) (out : Bit3 Fp) (_ : ProverData Fp) : Prop :=
  IsBool out.e ∧ IsBool out.r ∧ IsBool out.t

def bit3_ProverAssumptions (i : ℕ) (_ : Unit) (_ : ProverData Fp) (h : ProverHint Fp) : Prop :=
  IsBool (hintVal h (11 + 3 * i)) ∧ IsBool (hintVal h (12 + 3 * i)) ∧
    IsBool (hintVal h (13 + 3 * i))

theorem bit3_soundness (i : ℕ) :
    GeneralFormalCircuit.Soundness Fp (bit3_main i) (fun _ _ => True) bit3_Spec := by
  circuit_proof_start [bit3_main, bit3_Spec, assertBool, assertBool_Spec]
  simp_all

theorem bit3_completeness (i : ℕ) :
    GeneralFormalCircuit.Completeness Fp (bit3_main i) (bit3_ProverAssumptions i)
      (fun _ _ _ => True) := by
  circuit_proof_start [bit3_main, bit3_ProverAssumptions, assertBool, assertBool_Spec,
    hintExpr, hintVal]
  simp_all

def bit3 (i : ℕ) : GeneralFormalCircuit Fp unit Bit3 where
  main := bit3_main i
  elaborated := bit3_elaborated i
  Spec := bit3_Spec
  ProverAssumptions := bit3_ProverAssumptions i
  soundness := bit3_soundness i
  completeness := bit3_completeness i

/-! ## isOnCurve: `xx = x*x` wire, `x*xx` wire, one curve row (as `Baseline.isOnCurve`) -/

def isOnCurve_main (P : Var Point Fp) : Circuit Fp Unit := do
  let xx ← mulWire { a := P.x, b := P.x }
  let xxx ← mulWire { a := P.x, b := xx }
  assertZero (P.y * P.y - (xxx + curveA * P.x + curveB))

@[reducible] instance isOnCurve_elaborated :
    ElaboratedCircuit Fp Point unit isOnCurve_main := by elaborate_circuit

def isOnCurve_Spec (P : Point Fp) : Prop :=
  P.y ^ 2 = P.x ^ 3 + curveA * P.x + curveB

theorem isOnCurve_soundness :
    FormalAssertion.Soundness Fp isOnCurve_main (fun _ => True) isOnCurve_Spec := by
  circuit_proof_start [isOnCurve_main, isOnCurve_Spec, mulWire, mulWire_Spec]
  rcases h_input with ⟨rfl, rfl⟩
  obtain ⟨h1, h2, h3⟩ := h_holds
  rw [sub_eq_zero, h2, h1] at h3
  rw [pow_two, h3]
  ring

theorem isOnCurve_completeness :
    FormalAssertion.Completeness Fp isOnCurve_main (fun _ => True) isOnCurve_Spec := by
  circuit_proof_start [isOnCurve_main, isOnCurve_Spec, mulWire, mulWire_Spec]
  rcases h_input with ⟨rfl, rfl⟩
  obtain ⟨h1, h2⟩ := h_env
  rw [sub_eq_zero, h2, h1, ← pow_two, h_spec]
  ring

def isOnCurve : FormalAssertion Fp Point where
  main := isOnCurve_main
  elaborated := isOnCurve_elaborated
  Spec := isOnCurve_Spec
  soundness := isOnCurve_soundness
  completeness := isOnCurve_completeness

/-! ## sel: `x0 + b (x1 - x0)` on one wire (as `Optimized.sel` on non-constant operands) -/

structure SelInput (F : Type) where
  b : F
  x0 : F
  x1 : F
  deriving ProvableStruct

def sel_main (input : Var SelInput Fp) : Circuit Fp (Var field Fp) := do
  let w ← witnessField (input.x0 + input.b * (input.x1 - input.x0))
  assertZero (input.x0 + input.b * (input.x1 - input.x0) - w)
  return w

@[reducible] instance sel_elaborated :
    ElaboratedCircuit Fp SelInput field sel_main := by elaborate_circuit

def sel_Spec (input : SelInput Fp) (out : Fp) : Prop :=
  out = input.x0 + input.b * (input.x1 - input.x0)

theorem sel_soundness : Soundness Fp sel_main (fun _ => True) sel_Spec := by
  circuit_proof_start [sel_main, sel_Spec]
  rcases h_input with ⟨rfl, rfl, rfl⟩
  rw [sub_eq_zero] at h_holds
  exact h_holds.symm

theorem sel_completeness : Completeness Fp sel_main (fun _ => True) := by
  circuit_proof_start [sel_main]
  rcases h_input with ⟨rfl, rfl, rfl⟩
  simp_all

def sel : FormalCircuit Fp SelInput field where
  main := sel_main
  elaborated := sel_elaborated
  Spec := sel_Spec
  soundness := sel_soundness
  completeness := sel_completeness

/-! ## mux4: select among four point wires (as `Offset.mux4`: 3 `sel` per coordinate) -/

def mux4_main (input : Var Mux4Input Fp) : Circuit Fp (Var Point Fp) := do
  let t := input.table
  let ax ← sel { b := input.b0, x0 := t.p0.x, x1 := t.p1.x }
  let bx ← sel { b := input.b0, x0 := t.p2.x, x1 := t.p3.x }
  let x ← sel { b := input.b1, x0 := ax, x1 := bx }
  let ay ← sel { b := input.b0, x0 := t.p0.y, x1 := t.p1.y }
  let by_ ← sel { b := input.b0, x0 := t.p2.y, x1 := t.p3.y }
  let y ← sel { b := input.b1, x0 := ay, x1 := by_ }
  return { x, y }

@[reducible] instance mux4_elaborated :
    ElaboratedCircuit Fp Mux4Input Point mux4_main := by elaborate_circuit

def mux4_Assumptions (input : Mux4Input Fp) : Prop := IsBool input.b0 ∧ IsBool input.b1

def mux4_Spec (input : Mux4Input Fp) (out : Point Fp) : Prop :=
  out = input.table.select input.b0 input.b1

theorem mux4_soundness : Soundness Fp mux4_main mux4_Assumptions mux4_Spec := by
  circuit_proof_start [mux4_main, mux4_Assumptions, mux4_Spec, sel, sel_Spec, Table4.select]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h_holds
  obtain ⟨hb0 | hb0, hb1 | hb1⟩ := h_assumptions <;>
    simp only [hb0, hb1, one_ne_zero, ↓reduceIte, Point.mk.injEq] <;>
    simp only [hb0, hb1] at h1 h2 h3 h4 h5 h6 <;>
    rw [h3, h6, h1, h2, h4, h5] <;>
    constructor <;> ring

theorem mux4_completeness : Completeness Fp mux4_main mux4_Assumptions := by
  circuit_proof_start [mux4_main, sel]

def mux4 : FormalCircuit Fp Mux4Input Point where
  main := mux4_main
  elaborated := mux4_elaborated
  Assumptions := mux4_Assumptions
  Spec := mux4_Spec
  soundness := mux4_soundness
  completeness := mux4_completeness

/-! ## muxConst4: constant table, one shared bit product (as `Offset.muxConst4`) -/

/-- `v0 + (v1-v0) b0 + (v2-v0) b1 + (v3-v2-v1+v0) b01`. -/
def muxCoord (v0 v1 v2 v3 : Fp) (b0 b1 b01 : Expression Fp) : Expression Fp :=
  .const v0 + .const (v1 - v0) * b0 + .const (v2 - v0) * b1 + .const (v3 - v2 - v1 + v0) * b01

def muxConst4_main (i : Fin 128) (input : Var MuxConst4Input Fp) : Circuit Fp (Var Point Fp) := do
  let b01 ← mulWire { a := input.b0, b := input.b1 }
  let T := constTable i
  return { x := muxCoord T.p0.x T.p1.x T.p2.x T.p3.x input.b0 input.b1 b01,
           y := muxCoord T.p0.y T.p1.y T.p2.y T.p3.y input.b0 input.b1 b01 }

@[reducible] instance muxConst4_elaborated (i : Fin 128) :
    ElaboratedCircuit Fp MuxConst4Input Point (muxConst4_main i) := by elaborate_circuit

def muxConst4_Assumptions (input : MuxConst4Input Fp) : Prop := IsBool input.b0 ∧ IsBool input.b1

def muxConst4_Spec (i : Fin 128) (input : MuxConst4Input Fp) (out : Point Fp) : Prop :=
  out = (constTable i).select input.b0 input.b1

theorem muxConst4_soundness (i : Fin 128) :
    Soundness Fp (muxConst4_main i) muxConst4_Assumptions (muxConst4_Spec i) := by
  circuit_proof_start [muxConst4_main, muxConst4_Assumptions, muxConst4_Spec, mulWire,
    mulWire_Spec, muxCoord, Table4.select]
  generalize constTable i = T
  obtain ⟨⟨x0, y0⟩, ⟨x1, y1⟩, ⟨x2, y2⟩, ⟨x3, y3⟩⟩ := T
  rw [h_holds]
  obtain ⟨hb0 | hb0, hb1 | hb1⟩ := h_assumptions <;>
    simp only [hb0, hb1, one_ne_zero, ↓reduceIte, Point.mk.injEq] <;>
    constructor <;> ring

theorem muxConst4_completeness (i : Fin 128) :
    Completeness Fp (muxConst4_main i) muxConst4_Assumptions := by
  circuit_proof_start [muxConst4_main, mulWire]

def muxConst4 (i : Fin 128) : FormalCircuit Fp MuxConst4Input Point where
  main := muxConst4_main i
  elaborated := muxConst4_elaborated i
  Assumptions := muxConst4_Assumptions
  Spec := muxConst4_Spec i
  soundness := muxConst4_soundness i
  completeness := muxConst4_completeness i

end Solution.Projected.Gadgets
