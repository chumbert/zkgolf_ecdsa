/-
# Cost certificates for the standard circuit's gadgets

Every gadget of `StandardECDSA/Gadgets/` is certified here in the
`Challenge.CostR1CS` vocabulary:

* `CostIs c K` — `c` produces exactly `K.allocations` witness cells and
  `K.constraints` assertion rows at *every* offset.

`CostIs` is compositional (`CostIs.bind`, `CostIs.map`, `CostIs.witnessField`,
`CostIs.assertZero`, `CostIs.subcircuit`, …) and offset-independent, so the
certificates below are structural recursions mirroring the gadgets' own shape.
No `native_decide` is used, so the Lean compiler stays out of the trusted base.

## The `mat` helper

`mat` is the only helper whose cost depends on the *shape* of its argument: it
allocates one witness cell and one row per non-constant product node.  Its
certificate therefore uses `matCount`, a pure function of the expression's
structure, and `matCount_eq_zero_of_deg_le_one` collapses it on affine
arguments.  `matDeg_eq_zero` records that `matDeg` (the structural degree of
`mat`'s output) vanishes exactly when `deg` does, which is what makes `mat`'s
input-based branch condition equivalent to the output-based one.

Task T05/T07/T08/T09/T10.
-/

import StandardECDSA.Gadgets.Field
import StandardECDSA.Gadgets.Select
import StandardECDSA.Gadgets.Scalar
import StandardECDSA.Gadgets.Affine
import StandardECDSA.Gadgets.ELM
import Challenge.Utils.CostR1CS

namespace StandardECDSA.Gadgets

open Challenge.CostR1CS

/-! ## Count helpers -/

theorem CostIs.congr {F : Type} [FiniteField F] {α : Type} {c : Circuit F α} {K K' : Count}
    (h : CostIs c K) (hK : K = K') : CostIs c K' := by
  intro n; rw [h n, hK]

/-! ## `mat` -/

/-- Structural degree of `mat e`'s output. -/
def matDeg : E → ℕ
  | .var _ => 1
  | .const _ => 0
  | .add a b => max (matDeg a) (matDeg b)
  | .mul a b => if deg a = 0 ∨ deg b = 0 then matDeg a + matDeg b else 1

/-- Allocation/row count of `mat e`. -/
def matCount : E → Count
  | .var _ => Count.zero
  | .const _ => Count.zero
  | .add a b => matCount a + matCount b
  | .mul a b =>
      matCount a + matCount b + (if deg a = 0 ∨ deg b = 0 then Count.zero else ⟨1, 1⟩)

/-- `matDeg` vanishes exactly when `deg` does. -/
theorem matDeg_eq_zero (e : E) : matDeg e = 0 ↔ deg e = 0 := by
  induction e with
  | var v => simp [matDeg, deg]
  | const c => simp [matDeg, deg]
  | add a b iha ihb =>
      show max (matDeg a) (matDeg b) = 0 ↔ max (deg a) (deg b) = 0
      rw [Nat.max_eq_zero_iff, Nat.max_eq_zero_iff, iha, ihb]
  | mul a b iha ihb =>
      show (if deg a = 0 ∨ deg b = 0 then matDeg a + matDeg b else 1) = 0 ↔ deg a + deg b = 0
      by_cases h : deg a = 0 ∨ deg b = 0
      · rw [if_pos h, Nat.add_eq_zero_iff, iha, ihb, Nat.add_eq_zero_iff]
      · rw [if_neg h]
        refine ⟨fun hh => absurd hh (by decide), fun hh => ?_⟩
        rw [Nat.add_eq_zero_iff] at hh
        exact absurd (Or.inl hh.1) h

/-- `mat`'s allocation/row count. -/
theorem mat_cost (e : E) : CostIs (mat e) (matCount e) := by
  induction e with
  | var v => exact CostIs.pure _
  | const c => exact CostIs.pure _
  | add a b iha ihb =>
      simp only [mat, matCount]
      refine CostIs.congr (K := matCount a + (matCount b + Count.zero)) ?_ ?_
      · exact CostIs.bind iha (fun a' => CostIs.bind ihb (fun b' => CostIs.pure _))
      · show matCount a + (matCount b + Count.zero) = matCount a + matCount b
        rw [Count.add_zero]
  | mul a b iha ihb =>
      simp only [mat, matCount]
      by_cases h : deg a = 0 ∨ deg b = 0
      · simp only [if_pos h]
        refine CostIs.congr (K := matCount a + (matCount b + Count.zero)) ?_ ?_
        · exact CostIs.bind iha (fun a' => CostIs.bind ihb (fun b' => CostIs.pure _))
        · show matCount a + (matCount b + Count.zero) = matCount a + matCount b + Count.zero
          rw [Count.add_zero]
          exact (Count.add_zero _).symm
      · simp only [if_neg h]
        refine CostIs.congr
          (K := matCount a + (matCount b + (⟨1, 0⟩ + (⟨0, 1⟩ + Count.zero)))) ?_ ?_
        · exact CostIs.bind iha (fun a' => CostIs.bind ihb (fun b' =>
            CostIs.bind (CostIs.witnessField _) (fun w =>
              CostIs.bind (CostIs.assertZero _) (fun _ => CostIs.pure w))))
        · show matCount a + (matCount b + (⟨1, 0⟩ + (⟨0, 1⟩ + Count.zero))) =
            matCount a + matCount b + ⟨1, 1⟩
          rw [Count.add_zero]
          rfl

/-- `mat` allocates nothing on an affine expression. -/
theorem matCount_eq_zero_of_deg_le_one {e : E} (h : deg e ≤ 1) : matCount e = Count.zero := by
  induction e with
  | var v => rfl
  | const c => rfl
  | add a b iha ihb =>
      have h' : max (deg a) (deg b) ≤ 1 := h
      have ha : deg a ≤ 1 := by omega
      have hb : deg b ≤ 1 := by omega
      show matCount a + matCount b = Count.zero
      rw [iha ha, ihb hb]
      rfl
  | mul a b iha ihb =>
      have hd : deg a + deg b ≤ 1 := h
      have hz : deg a = 0 ∨ deg b = 0 := by omega
      have ha : deg a ≤ 1 := by omega
      have hb : deg b ≤ 1 := by omega
      show matCount a + matCount b + (if deg a = 0 ∨ deg b = 0 then Count.zero else ⟨1, 1⟩)
        = Count.zero
      rw [if_pos hz, iha ha, ihb hb]
      rfl

/-- `mm a b` costs one allocation and one row when both factors are affine and
non-constant. -/
theorem mm_cost_of_affine {a b : E} (ha : deg a = 1) (hb : deg b = 1) :
    CostIs (mm a b) ⟨1, 1⟩ := by
  have h := mat_cost (Expression.mul a b)
  rw [show matCount (Expression.mul a b) =
      matCount a + matCount b + (if deg a = 0 ∨ deg b = 0 then Count.zero else ⟨1, 1⟩)
      from rfl] at h
  rw [matCount_eq_zero_of_deg_le_one (by omega : deg a ≤ 1),
    matCount_eq_zero_of_deg_le_one (by omega : deg b ≤ 1),
    if_neg (by omega : ¬(deg a = 0 ∨ deg b = 0))] at h
  exact CostIs.congr h rfl

/-! ## Leaf gadgets -/

/-- `nonzero x` costs one allocation and one row. -/
theorem nonzero_cost (x : E) : CostIs (nonzero x) ⟨1, 1⟩ := by
  have h : CostIs (nonzero x) (⟨1, 0⟩ + (⟨0, 1⟩ + Count.zero)) := by
    unfold nonzero
    exact CostIs.bind (CostIs.witnessField _) (fun inv =>
      CostIs.bind (CostIs.assertZero _) (fun _ => CostIs.pure inv))
  exact CostIs.congr h rfl

/-- `assertBool b` costs one row and no allocation. -/
theorem assertBool_cost (b : E) : CostIs (assertBool b) ⟨0, 1⟩ :=
  CostIs.assertZero (b * b - b)

/-- `bitOf x j` costs one allocation and no row. -/
theorem bitOf_cost (x : E) (j : Nat) : CostIs (bitOf x j) ⟨1, 0⟩ :=
  CostIs.witnessField _

/-- `sel b x0 x1` costs one allocation and one row when `b`, `x0`, `x1` are
affine and `b` is non-constant. -/
theorem sel_cost_of_affine {b x0 x1 : E} (hb : deg b = 1) (h0 : deg x0 = 1)
    (h1 : deg x1 = 1) : CostIs (sel b x0 x1) ⟨1, 1⟩ := by
  have hsub : deg (x1 - x0) = 1 := by
    show max (deg x1) (deg (Expression.mul (Expression.const (-1)) x0)) = 1
    rw [show deg (Expression.mul (Expression.const (-1)) x0) = 0 + deg x0 from rfl, h0, h1]
    rfl
  have hprod : deg (Expression.mul b (x1 - x0)) = 2 := by
    show deg b + deg (x1 - x0) = 2
    rw [hb, hsub]
  have hsum : deg (x0 + Expression.mul b (x1 - x0)) = 2 := by
    show max (deg x0) (deg (Expression.mul b (x1 - x0))) = 2
    rw [h0, hprod]
    rfl
  have h := mat_cost (x0 + Expression.mul b (x1 - x0))
  rw [show matCount (x0 + Expression.mul b (x1 - x0)) =
      matCount x0 + matCount (Expression.mul b (x1 - x0)) from rfl] at h
  rw [show matCount (Expression.mul b (x1 - x0)) =
      matCount b + matCount (x1 - x0) +
        (if deg b = 0 ∨ deg (x1 - x0) = 0 then Count.zero else ⟨1, 1⟩) from rfl] at h
  rw [matCount_eq_zero_of_deg_le_one (by omega : deg x0 ≤ 1),
    matCount_eq_zero_of_deg_le_one (by omega : deg b ≤ 1),
    matCount_eq_zero_of_deg_le_one (by omega : deg (x1 - x0) ≤ 1),
    if_neg (by omega : ¬(deg b = 0 ∨ deg (x1 - x0) = 0))] at h
  exact CostIs.congr h rfl

end StandardECDSA.Gadgets
