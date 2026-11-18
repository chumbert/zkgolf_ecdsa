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

## Output degrees

Several gadgets' costs depend on the *degree* of the expression they receive
(`mat` allocates only for non-constant products).  The certificates therefore
carry, alongside `CostIs`, the fact that the gadget's output expression has a
known structural degree.  `CostIs.bind_dep` is the dependent bind that lets the
continuation's cost depend on a predicate of the intermediate value.

Task T05/T07/T08/T09/T10.
-/

import StandardECDSA.Gadgets.Field
import StandardECDSA.Gadgets.Select
import StandardECDSA.Gadgets.Scalar
import StandardECDSA.Gadgets.Affine
import StandardECDSA.Gadgets.ELM
import Challenge.Utils.CostR1CS

set_option maxRecDepth 100000

namespace StandardECDSA.Gadgets

open Challenge.CostR1CS

/-! ## Generic circuit-structure lemmas -/

theorem output_pure {F : Type} [FiniteField F] {α : Type} (a : α) (n : ℕ) :
    Circuit.output (pure a : Circuit F α) n = a := rfl

theorem output_bind {F : Type} [FiniteField F] {α β : Type} (f : Circuit F α)
    (g : α → Circuit F β) (n : ℕ) :
    Circuit.output (f >>= g) n =
      (g (Circuit.output f n)
        (n + Operations.localLength (Circuit.operations f n))).1 := rfl

theorem output_witnessField {F : Type} [FiniteField F] (e : Witgen.FExpr F) (n : ℕ) :
    Circuit.output (Circuit.witnessField e) n = Expression.var ⟨n⟩ := rfl

theorem output_assertZero {F : Type} [FiniteField F] (e : Expression F) (n : ℕ) :
    Circuit.output (Circuit.assertZero e) n = () := rfl

theorem fst_pure {F : Type} [FiniteField F] {α : Type} (a : α) (n : ℕ) :
    ((pure a : Circuit F α) n).1 = a := rfl

theorem fst_witnessField {F : Type} [FiniteField F] (e : Witgen.FExpr F) (n : ℕ) :
    ((Circuit.witnessField e) n).1 = Expression.var ⟨n⟩ := rfl

theorem CostIs.congr {F : Type} [FiniteField F] {α : Type} {c : Circuit F α} {K K' : Count}
    (h : CostIs c K) (hK : K = K') : CostIs c K' := by
  intro n; rw [h n, hK]

/-- Dependent bind: the continuation's cost may depend on a predicate `P` of the
intermediate value, provided `P` holds of `f`'s output at every offset. -/
theorem CostIs.bind_dep {F : Type} [FiniteField F] {α β : Type} {f : Circuit F α}
    {g : α → Circuit F β} {K₁ K₂ : Count} {P : α → Prop}
    (hf : CostIs f K₁) (hg : ∀ a, P a → CostIs (g a) K₂) (hP : ∀ n, P (Circuit.output f n)) :
    CostIs (f >>= g) (K₁ + K₂) := by
  intro n
  rw [Circuit.bind_operations_eq, Challenge.CostR1CS.Lemmas.operationCount_append, hf n]
  congr 1
  exact hg _ (hP n) _

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

/-- `matDeg` is the degree capped at one. -/
theorem matDeg_eq_min (e : E) : matDeg e = min (deg e) 1 := by
  induction e with
  | var v => rfl
  | const c => rfl
  | add a b iha ihb =>
      show max (matDeg a) (matDeg b) = min (max (deg a) (deg b)) 1
      rw [iha, ihb]
      omega
  | mul a b iha ihb =>
      show (if deg a = 0 ∨ deg b = 0 then matDeg a + matDeg b else 1) =
        min (deg a + deg b) 1
      rw [iha, ihb]
      by_cases h : deg a = 0 ∨ deg b = 0
      · rw [if_pos h]
        omega
      · rw [if_neg h]
        omega

/-- `mat`'s allocation/row count and output degree. -/
theorem mat_spec (e : E) :
    CostIs (mat e) (matCount e) ∧ ∀ n, deg (Circuit.output (mat e) n) = matDeg e := by
  induction e with
  | var v => exact ⟨CostIs.pure _, fun n => rfl⟩
  | const c => exact ⟨CostIs.pure _, fun n => rfl⟩
  | add a b iha ihb =>
      refine ⟨?_, ?_⟩
      · simp only [mat, matCount]
        refine CostIs.congr (K := matCount a + (matCount b + Count.zero)) ?_ ?_
        · exact CostIs.bind iha.1 (fun a' => CostIs.bind ihb.1 (fun b' => CostIs.pure _))
        · show matCount a + (matCount b + Count.zero) = matCount a + matCount b
          rw [Count.add_zero]
      · intro n
        simp only [mat, output_bind, output_pure]
        show max (deg (Circuit.output (mat a) n))
            (deg (Circuit.output (mat b)
              (n + Operations.localLength (Circuit.operations (mat a) n)))) =
          max (matDeg a) (matDeg b)
        rw [iha.2, ihb.2]
  | mul a b iha ihb =>
      refine ⟨?_, ?_⟩
      · simp only [mat, matCount]
        by_cases h : deg a = 0 ∨ deg b = 0
        · simp only [if_pos h]
          refine CostIs.congr (K := matCount a + (matCount b + Count.zero)) ?_ ?_
          · exact CostIs.bind iha.1 (fun a' => CostIs.bind ihb.1 (fun b' => CostIs.pure _))
          · show matCount a + (matCount b + Count.zero) = matCount a + matCount b + Count.zero
            rw [Count.add_zero]
            exact (Count.add_zero _).symm
        · simp only [if_neg h]
          refine CostIs.congr
            (K := matCount a + (matCount b + (⟨1, 0⟩ + (⟨0, 1⟩ + Count.zero)))) ?_ ?_
          · exact CostIs.bind iha.1 (fun a' => CostIs.bind ihb.1 (fun b' =>
              CostIs.bind (CostIs.witnessField _) (fun w =>
                CostIs.bind (CostIs.assertZero _) (fun _ => CostIs.pure w))))
          · show matCount a + (matCount b + (⟨1, 0⟩ + (⟨0, 1⟩ + Count.zero))) =
              matCount a + matCount b + ⟨1, 1⟩
            rw [Count.add_zero]
            rfl
      · intro n
        simp only [mat, output_bind]
        by_cases h : deg a = 0 ∨ deg b = 0
        · simp only [if_pos h, fst_pure]
          rw [show matDeg (Expression.mul a b) = matDeg a + matDeg b from by
            simp only [matDeg, if_pos h]]
          show deg (Circuit.output (mat a) n) +
              deg (Circuit.output (mat b)
                (n + Operations.localLength (Circuit.operations (mat a) n))) =
            matDeg a + matDeg b
          rw [iha.2, ihb.2]
        · simp only [if_neg h, output_bind, fst_witnessField]
          show 1 = matDeg (Expression.mul a b)
          rw [matDeg_eq_min, show deg (Expression.mul a b) = deg a + deg b from rfl,
            Nat.min_eq_right (by omega)]

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

/-! ## `mm` -/

/-- `mm a b` costs one allocation and one row, and returns a degree-1 expression,
when both factors are affine and non-constant. -/
theorem mm_spec {a b : E} (ha : deg a = 1) (hb : deg b = 1) :
    CostIs (mm a b) ⟨1, 1⟩ ∧ ∀ n, deg (Circuit.output (mm a b) n) = 1 := by
  have h := mat_spec (Expression.mul a b)
  rw [show matCount (Expression.mul a b) =
      matCount a + matCount b + (if deg a = 0 ∨ deg b = 0 then Count.zero else ⟨1, 1⟩)
      from rfl] at h
  rw [matCount_eq_zero_of_deg_le_one (by omega : deg a ≤ 1),
    matCount_eq_zero_of_deg_le_one (by omega : deg b ≤ 1),
    if_neg (by omega : ¬(deg a = 0 ∨ deg b = 0))] at h
  refine ⟨CostIs.congr h.1 rfl, fun n => ?_⟩
  show deg (Circuit.output (mat (Expression.mul a b)) n) = 1
  rw [h.2 n]
  show (if deg a = 0 ∨ deg b = 0 then matDeg a + matDeg b else 1) = 1
  rw [if_neg (by omega : ¬(deg a = 0 ∨ deg b = 0))]

/-! ## Leaf gadgets -/

/-- `nonzero x` costs one allocation and one row, and returns a degree-1
expression. -/
theorem nonzero_cost (x : E) :
    CostIs (nonzero x) ⟨1, 1⟩ ∧ ∀ n, deg (Circuit.output (nonzero x) n) = 1 := by
  refine ⟨?_, ?_⟩
  · have h : CostIs (nonzero x) (⟨1, 0⟩ + (⟨0, 1⟩ + Count.zero)) := by
      unfold nonzero
      exact CostIs.bind (CostIs.witnessField _) (fun inv =>
        CostIs.bind (CostIs.assertZero _) (fun _ => CostIs.pure inv))
    exact CostIs.congr h rfl
  · intro n
    simp only [nonzero, output_bind, output_pure, output_witnessField]
    rfl

/-- `assertBool b` costs one row and no allocation. -/
theorem assertBool_cost (b : E) : CostIs (assertBool b) ⟨0, 1⟩ :=
  CostIs.assertZero (b * b - b)

/-- `bitOf x j` costs one allocation, no row, and returns a degree-1 expression. -/
theorem bitOf_spec (x : E) (j : Nat) :
    CostIs (bitOf x j) ⟨1, 0⟩ ∧ ∀ n, deg (Circuit.output (bitOf x j) n) = 1 :=
  ⟨CostIs.witnessField _, fun n => rfl⟩

/-- `sel b x0 x1` costs one allocation and one row, and returns a degree-1
expression, when `b`, `x0`, `x1` are affine and `b` is non-constant. -/
theorem sel_cost {b x0 x1 : E} (hb : deg b = 1) (h0 : deg x0 = 1) (h1 : deg x1 = 1) :
    CostIs (sel b x0 x1) ⟨1, 1⟩ ∧ ∀ n, deg (Circuit.output (sel b x0 x1) n) = 1 := by
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
  have h := mat_spec (x0 + Expression.mul b (x1 - x0))
  rw [show matCount (x0 + Expression.mul b (x1 - x0)) =
      matCount x0 + matCount (Expression.mul b (x1 - x0)) from rfl] at h
  rw [show matCount (Expression.mul b (x1 - x0)) =
      matCount b + matCount (x1 - x0) +
        (if deg b = 0 ∨ deg (x1 - x0) = 0 then Count.zero else ⟨1, 1⟩) from rfl] at h
  rw [matCount_eq_zero_of_deg_le_one (by omega : deg x0 ≤ 1),
    matCount_eq_zero_of_deg_le_one (by omega : deg b ≤ 1),
    matCount_eq_zero_of_deg_le_one (by omega : deg (x1 - x0) ≤ 1),
    if_neg (by omega : ¬(deg b = 0 ∨ deg (x1 - x0) = 0))] at h
  refine ⟨CostIs.congr h.1 rfl, fun n => ?_⟩
  show deg (Circuit.output (mat (x0 + Expression.mul b (x1 - x0))) n) = 1
  rw [h.2 n]
  show max (matDeg x0) (matDeg (Expression.mul b (x1 - x0))) = 1
  rw [matDeg_eq_min, matDeg_eq_min, h0, hprod]
  rfl

/-! ## Multiplexers -/

/-- `muxConst4 b0 b1 tab` costs one allocation and one row. -/
theorem muxConst4_cost {b0 b1 : E} (h0 : deg b0 = 1) (h1 : deg b1 = 1)
    (tab : Array (Fp × Fp)) : CostIs (muxConst4 b0 b1 tab) ⟨1, 1⟩ := by
  have h : CostIs (muxConst4 b0 b1 tab) (⟨1, 1⟩ + Count.zero) := by
    simp only [muxConst4]
    exact CostIs.bind (mm_spec h0 h1).1 (fun b01 => CostIs.pure _)
  exact CostIs.congr h rfl

/-- `mux4 b0 b1 p0 p1 p2 p3` costs six allocations and six rows when the
selectors and all four points are affine and the selectors are non-constant. -/
theorem mux4_cost {b0 b1 : E} (hb0 : deg b0 = 1) (hb1 : deg b1 = 1)
    {p0 p1 p2 p3 : Pt}
    (h0 : deg p0.1 = 1 ∧ deg p0.2 = 1) (h1 : deg p1.1 = 1 ∧ deg p1.2 = 1)
    (h2 : deg p2.1 = 1 ∧ deg p2.2 = 1) (h3 : deg p3.1 = 1 ∧ deg p3.2 = 1) :
    CostIs (mux4 b0 b1 p0 p1 p2 p3) ⟨6, 6⟩ := by
  have h : CostIs (mux4 b0 b1 p0 p1 p2 p3)
      (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + Count.zero)))))) := by
    simp only [mux4]
    refine CostIs.bind_dep (P := fun a => deg a = 1) (sel_cost hb0 h0.1 h1.1).1 ?_ (sel_cost hb0 h0.1 h1.1).2
    intro ax hax
    refine CostIs.bind_dep (P := fun a => deg a = 1) (sel_cost hb0 h2.1 h3.1).1 ?_ (sel_cost hb0 h2.1 h3.1).2
    intro bx hbx
    refine CostIs.bind_dep (P := fun a => deg a = 1) (sel_cost hb1 hax hbx).1 ?_ ?_
    · intro x _
      refine CostIs.bind_dep (P := fun a => deg a = 1) (sel_cost hb0 h0.2 h1.2).1 ?_ (sel_cost hb0 h0.2 h1.2).2
      intro ay hay
      refine CostIs.bind_dep (P := fun a => deg a = 1) (sel_cost hb0 h2.2 h3.2).1 ?_ (sel_cost hb0 h2.2 h3.2).2
      intro by' hby'
      refine CostIs.bind_dep (P := fun a => deg a = 1) (sel_cost hb1 hay hby').1 ?_ ?_
      · intro y _
        exact CostIs.pure _
      · intro n
        exact (sel_cost hb1 hay hby').2 n
    · intro n
      exact (sel_cost hb1 hax hbx).2 n
  exact CostIs.congr h rfl

/-! ## Affine and ELM gadgets -/

/-- `affAdd p q` costs four allocations and four rows. -/
theorem affAdd_cost (p q : Pt) : CostIs (affAdd p q) ⟨4, 4⟩ := by
  have h : CostIs (affAdd p q)
      (⟨1, 1⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + Count.zero))))))) := by
    simp only [affAdd]
    exact CostIs.bind (nonzero_cost _).1 (fun inv =>
      CostIs.bind (CostIs.witnessField _) (fun l =>
        CostIs.bind (CostIs.assertZero _) (fun _ =>
          CostIs.bind (CostIs.witnessField _) (fun x =>
            CostIs.bind (CostIs.assertZero _) (fun _ =>
              CostIs.bind (CostIs.witnessField _) (fun y =>
                CostIs.bind (CostIs.assertZero _) (fun _ => CostIs.pure _)))))))
  exact CostIs.congr h rfl

/-- `affDouble p` costs four allocations and four rows when `p.x` is affine and
non-constant. -/
theorem affDouble_cost {p : Pt} (hx : deg p.1 = 1) : CostIs (affDouble p) ⟨4, 4⟩ := by
  have h : CostIs (affDouble p)
      (⟨1, 1⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + Count.zero))))))) := by
    simp only [affDouble]
    exact CostIs.bind (mm_spec hx hx).1 (fun xx =>
      CostIs.bind (CostIs.witnessField _) (fun l =>
        CostIs.bind (CostIs.assertZero _) (fun _ =>
          CostIs.bind (CostIs.witnessField _) (fun x =>
            CostIs.bind (CostIs.assertZero _) (fun _ =>
              CostIs.bind (CostIs.witnessField _) (fun y =>
                CostIs.bind (CostIs.assertZero _) (fun _ => CostIs.pure _)))))))
  exact CostIs.congr h rfl

/-- `elmCore p q` costs four allocations and four rows. -/
theorem elmCore_cost (p q : Pt) : CostIs (elmCore p q) ⟨4, 4⟩ := by
  have h : CostIs (elmCore p q)
      (⟨1, 1⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + Count.zero))))))) := by
    simp only [elmCore]
    exact CostIs.bind (nonzero_cost _).1 (fun inv1 =>
      CostIs.bind (CostIs.witnessField _) (fun l1 =>
        CostIs.bind (CostIs.assertZero _) (fun _ =>
          CostIs.bind (CostIs.witnessField _) (fun xu =>
            CostIs.bind (CostIs.assertZero _) (fun _ =>
              CostIs.bind (CostIs.witnessField _) (fun l2 =>
                CostIs.bind (CostIs.assertZero _) (fun _ => CostIs.pure _)))))))
  exact CostIs.congr h rfl

/-- `elm p q` costs six allocations and six rows. -/
theorem elm_cost (p q : Pt) : CostIs (elm p q) ⟨6, 6⟩ := by
  have h : CostIs (elm p q)
      (⟨4, 4⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + (⟨1, 0⟩ + (⟨0, 1⟩ + Count.zero))))) := by
    simp only [elm]
    exact CostIs.bind (elmCore_cost p q) (fun xu_l2 =>
      CostIs.bind (CostIs.witnessField _) (fun x =>
        CostIs.bind (CostIs.assertZero _) (fun _ =>
          CostIs.bind (CostIs.witnessField _) (fun y =>
            CostIs.bind (CostIs.assertZero _) (fun _ => CostIs.pure _)))))
  exact CostIs.congr h rfl

/-- `elmTo p q target` costs four allocations and six rows. -/
theorem elmTo_cost (p q target : Pt) : CostIs (elmTo p q target) ⟨4, 6⟩ := by
  have h : CostIs (elmTo p q target) (⟨4, 4⟩ + (⟨0, 1⟩ + (⟨0, 1⟩ + Count.zero))) := by
    simp only [elmTo]
    exact CostIs.bind (elmCore_cost p q) (fun xu_l2 =>
      CostIs.bind (CostIs.assertZero _) (fun _ =>
        CostIs.bind (CostIs.assertZero _) (fun _ => CostIs.pure _)))
  exact CostIs.congr h rfl

/-! ## Lazy zero assertions -/

/-- Cost of materialising the remaining product terms. -/
def azlLoopCost : List (Fp × E) → Count
  | [] => Count.zero
  | it :: rest => matCount it.2 + azlLoopCost rest

theorem azlLoop_cost (acc : E) (l : List (Fp × E)) :
    CostIs (azlLoop acc l) (azlLoopCost l) := by
  induction l generalizing acc with
  | nil => exact CostIs.pure acc
  | cons it rest ih =>
      simp only [azlLoop, azlLoopCost]
      exact CostIs.bind (mat_spec it.2).1 (fun w => ih _)

theorem azlLinLoop_cost (acc : E) (l : List (Fp × E)) :
    CostIs (azlLinLoop acc l) Count.zero := by
  induction l generalizing acc with
  | nil => exact CostIs.pure acc
  | cons it rest ih => exact ih _

/-- Cost of `assertZeroLazy e`, as a function of the flattened expression. -/
def assertZeroLazyCost (e : E) : Count :=
  match (flat 1 e).filter (fun it => isProd it.2) with
  | [] => ⟨0, 1⟩
  | (c, .mul a b) :: rest => matCount a + (matCount b + (azlLoopCost rest + ⟨0, 1⟩))
  | _ => Count.zero

theorem assertZeroLazy_cost (e : E) : CostIs (assertZeroLazy e) (assertZeroLazyCost e) := by
  unfold assertZeroLazyCost
  cases h : (flat 1 e).filter (fun it => isProd it.2) with
  | nil =>
      simp only [assertZeroLazy, h]
      exact CostIs.assertZero e
  | cons it rest =>
      obtain ⟨c, t⟩ := it
      cases t with
      | var v => simp only [assertZeroLazy, h]; exact CostIs.pure ()
      | const c' => simp only [assertZeroLazy, h]; exact CostIs.pure ()
      | add a b => simp only [assertZeroLazy, h]; exact CostIs.pure ()
      | mul a b =>
          simp only [assertZeroLazy, h]
          refine CostIs.congr
            (K := matCount a + (matCount b + (azlLoopCost rest + (Count.zero + ⟨0, 1⟩)))) ?_ ?_
          · exact CostIs.bind (mat_spec a).1 (fun a' =>
              CostIs.bind (mat_spec b).1 (fun b' =>
                CostIs.bind (azlLoop_cost _ rest) (fun acc =>
                  CostIs.bind (azlLinLoop_cost acc _) (fun acc' => CostIs.assertZero acc'))))
          · show matCount a + (matCount b + (azlLoopCost rest + (Count.zero + ⟨0, 1⟩))) =
              matCount a + (matCount b + (azlLoopCost rest + ⟨0, 1⟩))
            rw [Count.zero_add]

/-! ## Order comparators -/

/-- Cost of the comparison loop: one allocation and one row per zero run. -/
def ltLoopCost : List (Nat × Nat × Bool) → Count
  | [] => Count.zero
  | (hi, lo, bit) :: rest => (if bit then Count.zero else ⟨1, 1⟩) + ltLoopCost rest

theorem ltLoop_cost (a : Nat → E) (missing : E) (l : List (Nat × Nat × Bool)) :
    CostIs (ltLoop a missing l) (ltLoopCost l) := by
  induction l generalizing missing with
  | nil => exact CostIs.pure ()
  | cons it rest ih =>
      obtain ⟨hi, lo, bit⟩ := it
      simp only [ltLoop, ltLoopCost]
      split
      · rw [Count.zero_add]
        exact ih _
      · refine CostIs.congr (K := ⟨1, 0⟩ + (⟨0, 1⟩ + ltLoopCost rest)) ?_ ?_
        · exact CostIs.bind (CostIs.witnessField _) (fun q =>
            CostIs.bind (CostIs.assertZero _) (fun _ => ih _))
        · show ⟨1, 0⟩ + (⟨0, 1⟩ + ltLoopCost rest) = ⟨1, 1⟩ + ltLoopCost rest
          rw [← Count.add_assoc]
          rfl

theorem ltLoopGuarded_cost (a : Nat → E) (guard missing : E) (l : List (Nat × Nat × Bool)) :
    CostIs (ltLoopGuarded a guard missing l) (ltLoopCost l) := by
  induction l generalizing missing with
  | nil => exact CostIs.pure ()
  | cons it rest ih =>
      obtain ⟨hi, lo, bit⟩ := it
      simp only [ltLoopGuarded, ltLoopCost]
      split
      · rw [Count.zero_add]
        exact ih _
      · refine CostIs.congr (K := ⟨1, 0⟩ + (⟨0, 1⟩ + ltLoopCost rest)) ?_ ?_
        · exact CostIs.bind (CostIs.witnessField _) (fun q =>
            CostIs.bind (CostIs.assertZero _) (fun _ => ih _))
        · show ⟨1, 0⟩ + (⟨0, 1⟩ + ltLoopCost rest) = ⟨1, 1⟩ + ltLoopCost rest
          rw [← Count.add_assoc]
          rfl

theorem assertLtOrderOf_cost (bound : Nat) (a : Nat → E) :
    CostIs (assertLtOrderOf bound a) (ltLoopCost (boundRunsOf bound)) :=
  ltLoop_cost a (cst 0) (boundRunsOf bound)

theorem assertLtOrderGuardedOf_cost (bound : Nat) (guard : E) (a : Nat → E) :
    CostIs (assertLtOrderGuardedOf bound guard a) (ltLoopCost (boundRunsOf bound)) :=
  ltLoopGuarded_cost a guard (cst 0) (boundRunsOf bound)

/-- The `n - 1` comparator costs 34 allocations and 34 rows. -/
theorem assertLtOrderOf_cost_n (a : Nat → E) :
    CostIs (assertLtOrderOf nSubOne a) ⟨34, 34⟩ := by
  have h := assertLtOrderOf_cost nSubOne a
  have hc : ltLoopCost (boundRunsOf nSubOne) = ⟨34, 34⟩ := by decide
  rw [hc] at h
  exact h

/-- The guarded `(p - n) - 1` comparator costs 34 allocations and 34 rows. -/
theorem assertLtOrderGuardedOf_cost_p (guard : E) (a : Nat → E) :
    CostIs (assertLtOrderGuardedOf pSubNSubOne guard a) ⟨34, 34⟩ := by
  have h := assertLtOrderGuardedOf_cost pSubNSubOne guard a
  have hc : ltLoopCost (boundRunsOf pSubNSubOne) = ⟨34, 34⟩ := by decide
  rw [hc] at h
  exact h

/-! ## Curve assertions -/

/-- `flat` of the on-curve expression, for wire-variable coordinates. -/
theorem flat_isOnCurve (vx vy : Variable Fp) (xx : E) (hxx : deg xx = 1) :
    flat 1 (.mul (.var vy) (.var vy) - (.mul (.var vx) xx + sc pa (.var vx) + cst pb))
      = [(1, .mul (.var vy) (.var vy)), (-1, .mul (.var vx) xx),
          (-1 * pa, .var vx), (-1, .const pb)] := by
  have hxx' : Challenge.CostR1CS.degree xx = 1 := hxx
  show flat 1 (Expression.add (.mul (.var vy) (.var vy))
    (Expression.mul (Expression.const (-1))
      (Expression.add (Expression.add (Expression.mul (.var vx) xx)
        (Expression.mul (Expression.const pa) (.var vx))) (Expression.const pb)))) = _
  simp [flat, hxx', deg, Challenge.CostR1CS.degree, constVal, Expression.eval]

/-- `isOnCurve` on two wire variables costs two allocations and three rows. -/
theorem isOnCurve_cost_var (vx vy : Variable Fp) :
    CostIs (isOnCurve (.var vx) (.var vy)) ⟨2, 3⟩ := by
  have hmm := mm_spec (a := .var vx) (b := .var vx) rfl rfl
  have hazl : ∀ xx : E, deg xx = 1 → assertZeroLazyCost
      (.mul (.var vy) (.var vy) - (.mul (.var vx) xx + sc pa (.var vx) + cst pb)) = ⟨1, 2⟩ := by
    intro xx hxx
    unfold assertZeroLazyCost
    rw [flat_isOnCurve vx vy xx hxx]
    simp only [List.filter, isProd, matCount, azlLoopCost, Count.zero, hxx,
      matCount_eq_zero_of_deg_le_one (by omega : deg xx ≤ 1)]
    rfl
  have h : CostIs (mm (.var vx) (.var vx) >>= fun xx => assertZeroLazy
      (.mul (.var vy) (.var vy) - (.mul (.var vx) xx + sc pa (.var vx) + cst pb)))
      (⟨1, 1⟩ + ⟨1, 2⟩) :=
    CostIs.bind_dep (P := fun xx => deg xx = 1) hmm.1
      (fun xx hx => CostIs.congr (assertZeroLazy_cost _) (hazl xx hx)) hmm.2
  exact CostIs.congr h rfl

/-- `pointEquality` on wire variables costs no allocation and two rows. -/
theorem pointEquality_cost_var (vx vy vz vpx vpy : Variable Fp) :
    CostIs (pointEquality (.var vx) (.var vy) (.var vz) (.var vpx) (.var vpy)) ⟨0, 2⟩ := by
  have hmat : CostIs (mat (.var vz)) Count.zero := (mat_spec (.var vz)).1
  have h1 : ∀ z' : E, deg z' = 1 → assertZeroLazyCost (.var vx - .mul z' (.var vpx)) = ⟨0, 1⟩ := by
    intro z' hz
    have hz' : Challenge.CostR1CS.degree z' = 1 := hz
    unfold assertZeroLazyCost
    rw [show flat 1 (.var vx - .mul z' (.var vpx))
        = [(1, .var vx), (-1, .mul z' (.var vpx))] from by
      show flat 1 (Expression.add (.var vx)
        (Expression.mul (Expression.const (-1)) (.mul z' (.var vpx)))) = _
      simp [flat, deg, Challenge.CostR1CS.degree, constVal, Expression.eval, hz']]
    simp only [List.filter, isProd, matCount, azlLoopCost, Count.zero,
      matCount_eq_zero_of_deg_le_one (by omega : deg z' ≤ 1)]
    rfl
  have h2 : ∀ z' : E, deg z' = 1 → assertZeroLazyCost (.var vy - .mul z' (.var vpy)) = ⟨0, 1⟩ := by
    intro z' hz
    have hz' : Challenge.CostR1CS.degree z' = 1 := hz
    unfold assertZeroLazyCost
    rw [show flat 1 (.var vy - .mul z' (.var vpy))
        = [(1, .var vy), (-1, .mul z' (.var vpy))] from by
      show flat 1 (Expression.add (.var vy)
        (Expression.mul (Expression.const (-1)) (.mul z' (.var vpy)))) = _
      simp [flat, deg, Challenge.CostR1CS.degree, constVal, Expression.eval, hz']]
    simp only [List.filter, isProd, matCount, azlLoopCost, Count.zero,
      matCount_eq_zero_of_deg_le_one (by omega : deg z' ≤ 1)]
    rfl
  have h : CostIs (mat (.var vz) >>= fun z' =>
      assertZeroLazy (.var vx - .mul z' (.var vpx)) >>= fun _ =>
      assertZeroLazy (.var vy - .mul z' (.var vpy))) (Count.zero + (⟨0, 1⟩ + ⟨0, 1⟩)) :=
    CostIs.bind_dep (P := fun z' => deg z' = 1) hmat
      (fun z' hz => CostIs.bind (CostIs.congr (assertZeroLazy_cost _) (h1 z' hz))
        (fun _ => CostIs.congr (assertZeroLazy_cost _) (h2 z' hz)))
      (fun n => (mat_spec (.var vz)).2 n)
  exact CostIs.congr h rfl

end StandardECDSA.Gadgets
