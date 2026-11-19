/-
# Honest-witness denominators (task G2-b, ladder part) — the final step

`CompleteWitness`'s six ladder fields `hj1`, `hj2`, `hjf1`..`hjf4` are the
ladder's per-step and final-step denominators.  `jointLadder_denominators`
(`HonestLadder.lean`) derives them from the phase's *soundness* `hc`, which is
circular: `hc` itself needs the final `elmTo` rows, which need the group
identity, which needs the denominators.

This module breaks the circle by reading everything from the phase's *local
witnesses* (`UsesLocalWitnessesCompleteness`) instead:

* `elmToXu_group_of_ulwc` — the `elmTo` middle `x` is the group sum's `x`,
  from rows 1–4 only (no `elmTo` soundness needed);
* `jointLadder_final_ulwc` — the final step's local witnesses;
* `hjf1_dx_of_ulwc` — the first final denominator `x(T₂₅₅) - x(C₂₅₅)`, from the
  `ladStep` slots at `j = 255` (coefficients 4 and 2);
* `hjf2_dx_of_ulwc` — the second final denominator `x(C₂₅₅) - x(C₂₅₅ + T₂₅₅)`,
  from the `ladDbl` slots at `j = 255` (coefficients 1 and 3).

Every proof is complete; no new axioms and no `native_decide`.
-/

import StandardECDSA.Witness.HonestLadderFinal
import StandardECDSA.Phases.HonestLadderJoint
import StandardECDSA.Witness.HonestShiftedFields
import StandardECDSA.Phases.HonestFixedBase

namespace StandardECDSA

open WeierstrassCurve StandardECDSA StandardECDSA.Gadgets StandardECDSA.Phases
  StandardECDSA.Math
open StandardECDSA.Math.FixedTables

/-! ## `elmTo`'s middle `x`, from local witnesses only -/

/-- The `x`-coordinate `xu` allocated by `elmTo`'s `elmCore` is the
`x`-coordinate of `p + q` in the group — from the local witnesses alone. -/
theorem elmToXu_group_of_ulwc (p q target : Pt) (env : ProverEnvironment Fp) (m : Nat)
    (hA : NS (Expression.eval env.toEnvironment p.1) (Expression.eval env.toEnvironment p.2))
    (hB : NS (Expression.eval env.toEnvironment q.1) (Expression.eval env.toEnvironment q.2))
    (hDx : Expression.eval env.toEnvironment q.1 - Expression.eval env.toEnvironment p.1 ≠ 0)
    (hw : env.UsesLocalWitnessesCompleteness m ((elmTo p q target).operations m)) :
    ∃ hU : NS (env.get (m + 2))
        (ElmAlgebra.elmMiddleY (Expression.eval env.toEnvironment p.1)
          (Expression.eval env.toEnvironment p.2) (env.get (m + 2)) (env.get (m + 1))),
      Affine.Point.some (env.get (m + 2))
          (ElmAlgebra.elmMiddleY (Expression.eval env.toEnvironment p.1)
            (Expression.eval env.toEnvironment p.2) (env.get (m + 2)) (env.get (m + 1))) hU
        = Affine.Point.some (Expression.eval env.toEnvironment p.1)
            (Expression.eval env.toEnvironment p.2) hA
          + Affine.Point.some (Expression.eval env.toEnvironment q.1)
            (Expression.eval env.toEnvironment q.2) hB := by
  simp only [elmTo, elmCore, nonzero, circuit_norm, pm] at hw
  obtain ⟨r1, r2, r3, r4⟩ := hw
  simp only [eval_cst, eval_sc] at r1 r2 r3 r4
  rw [show m + 1 + 1 + 1 = m + 3 from by omega] at r4
  rw [show m + 1 + 1 = m + 2 from by omega] at r3 r4
  have h1 : env.get (m + 1) * (Expression.eval env.toEnvironment q.1
      - Expression.eval env.toEnvironment p.1)
      = Expression.eval env.toEnvironment q.2 - Expression.eval env.toEnvironment p.2 := by
    rw [r2, r1, mul_assoc, inv_mul_cancel₀ hDx, mul_one]
  have h2 : env.get (m + 1) * env.get (m + 1)
      = Expression.eval env.toEnvironment p.1 + Expression.eval env.toEnvironment q.1
        + env.get (m + 2) := by
    rw [r3]
    ring
  have hYU : env.get (m + 1) * (Expression.eval env.toEnvironment p.1 - env.get (m + 2))
      = Expression.eval env.toEnvironment p.2
        + ElmAlgebra.elmMiddleY (Expression.eval env.toEnvironment p.1)
            (Expression.eval env.toEnvironment p.2) (env.get (m + 2)) (env.get (m + 1)) := by
    simp only [ElmAlgebra.elmMiddleY]
    ring
  have hU := ElmAlgebra.affine_add_onCurve params.a params.b
    (Expression.eval env.toEnvironment p.1) (Expression.eval env.toEnvironment p.2)
    (Expression.eval env.toEnvironment q.1) (Expression.eval env.toEnvironment q.2)
    (env.get (m + 2))
    (ElmAlgebra.elmMiddleY (Expression.eval env.toEnvironment p.1)
      (Expression.eval env.toEnvironment p.2) (env.get (m + 2)) (env.get (m + 1)))
    (env.get (m + 1)) (ns_equation _ _ hA) (ns_equation _ _ hB) hDx h1 h2 hYU
  refine ⟨Math.AffineBridge.short_nonsingular params _ _ hU, ?_⟩
  exact Math.AffineBridge.affine_add_eq_group params
    (Expression.eval env.toEnvironment p.1) (Expression.eval env.toEnvironment p.2)
    (Expression.eval env.toEnvironment q.1) (Expression.eval env.toEnvironment q.2)
    (env.get (m + 2))
    (ElmAlgebra.elmMiddleY (Expression.eval env.toEnvironment p.1)
      (Expression.eval env.toEnvironment p.2) (env.get (m + 2)) (env.get (m + 1)))
    (env.get (m + 1))
    (Math.AffineBridge.short_nonsingular params _ _ (ns_equation _ _ hA))
    (Math.AffineBridge.short_nonsingular params _ _ (ns_equation _ _ hB))
    (Math.AffineBridge.short_nonsingular params _ _ hU) hDx h1 h2 hYU

/-! ## The ladder's final step, from local witnesses -/

/-- Splitting the ladder's local witnesses into the 255-step fold and the final
step. -/
theorem jointLadder_final_ulwc (acc0 : Pt) (tables : Tables) (rb sb : Vector E 256)
    (target : Pt) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n
      ((jointLadder acc0 tables rb sb target).operations n)) :
    env.UsesLocalWitnessesCompleteness (n + 3060)
        ((mux4W (rb.get ⟨0, by omega⟩) (sb.get ⟨0, by omega⟩)
          (tables.x0 255) (tables.x1 255) (tables.x2 255) (tables.x3 255)).operations
          (n + 3060))
      ∧ env.UsesLocalWitnessesCompleteness (n + 3060 + 6)
        ((elmTo (jlOut acc0 tables rb sb n)
          ((mux4W (rb.get ⟨0, by omega⟩) (sb.get ⟨0, by omega⟩)
            (tables.x0 255) (tables.x1 255) (tables.x2 255) (tables.x3 255)).output
            (n + 3060)) target).operations (n + 3060 + 6)) := by
  rw [jointLadder_ops] at hw
  rw [ulwc_append] at hw
  simp only [jointLadderFold_localLength] at hw
  obtain ⟨-, hw2⟩ := hw
  have hw2' : env.UsesLocalWitnessesCompleteness (n + 3060)
      ((jointLadderFinal tables rb sb (jlOut acc0 tables rb sb n) target).operations
        (n + 3060)) := by
    rw [← jlOut_eq] at hw2
    exact hw2
  rw [jointLadderFinal_ops] at hw2'
  rw [ulwc_append] at hw2'
  simp only [mux4W_localLength] at hw2'
  exact hw2'

/-! ## The two final denominators, from local witnesses -/

set_option linter.constructorNameAsVariable false in
/-- `hjf1`: the first denominator of the final `elmTo` does not vanish.  The
accumulator is `C₂₅₅ = H + B₁` and the last table entry is `T₂₅₅ = -3·H + B₀`,
so the two bad equations are `[4]H = B₀ - B₁` and `[2]H = B₀ + B₁` — the
`ladStep` slots at `j = 255`. -/
theorem hjf1_dx_of_ulwc (env : ProverEnvironment Fp) (eb : Vector E 256)
    (rb sb : Vector E 256) (Qpt Rpt : Affine.Point Wp) (H : AffinePoint K)
    (hH : H.IsOnCurve params)
    (hgood : GoodOffset H hH (famOf env.toEnvironment eb rb sb Qpt Rpt))
    (acc0 : Pt) (tables : Tables) (target : Pt) (n : Nat)
    (hacc0 : ∃ hns : NS (Expression.eval env.toEnvironment acc0.1)
        (Expression.eval env.toEnvironment acc0.2),
      Affine.Point.some (Expression.eval env.toEnvironment acc0.1)
        (Expression.eval env.toEnvironment acc0.2) hns = -goodOffsetAffinePt H hH)
    (hb : ∀ k : Fin 256,
      Expression.eval env.toEnvironment (rb.get k) = 0 ∨
        Expression.eval env.toEnvironment (rb.get k) = 1)
    (hb' : ∀ k : Fin 256,
      Expression.eval env.toEnvironment (sb.get k) = 0 ∨
        Expression.eval env.toEnvironment (sb.get k) = 1)
    (htab : ∀ (j : Nat) (hj : j < 256) (v w : Fp), (v = 0 ∨ v = 1) → (w = 0 ∨ w = 1) →
      ∃ hns : NS (if v = 0 then
            (if w = 0 then Expression.eval env.toEnvironment (tables.x0 j).1
              else Expression.eval env.toEnvironment (tables.x2 j).1)
          else (if w = 0 then Expression.eval env.toEnvironment (tables.x1 j).1
            else Expression.eval env.toEnvironment (tables.x3 j).1))
          (if v = 0 then
            (if w = 0 then Expression.eval env.toEnvironment (tables.x0 j).2
              else Expression.eval env.toEnvironment (tables.x2 j).2)
          else (if w = 0 then Expression.eval env.toEnvironment (tables.x1 j).2
            else Expression.eval env.toEnvironment (tables.x3 j).2)),
        Affine.Point.some _ _ hns
          = (3 * sigma j) • goodOffsetAffinePt H hH
            + (if v = 1 then (1 : ℤ) else 0) • Qpt
            + (if w = 1 then (1 : ℤ) else 0) • Rpt)
    (hw : env.UsesLocalWitnessesCompleteness n
      ((jointLadder acc0 tables rb sb target).operations n)) :
    Expression.eval env.toEnvironment
        ((mux4W (rb.get ⟨0, by omega⟩) (sb.get ⟨0, by omega⟩)
          (tables.x0 255) (tables.x1 255) (tables.x2 255) (tables.x3 255)).output
          (n + 3060)).1
      - Expression.eval env.toEnvironment (jlOut acc0 tables rb sb n).1 ≠ 0 := by
  classical
  obtain ⟨hm, -⟩ := jointLadder_final_ulwc acc0 tables rb sb target env n hw
  obtain ⟨hns255, hval255⟩ :=
    jointLadder_ladInv_255_of_ulwc env n H hH Qpt Rpt eb rb sb acc0 tables target
      hgood hw hacc0 hb hb' htab
  obtain ⟨hTm, hTval⟩ := mux4W_Tpt env.toEnvironment (goodOffsetAffinePt H hH) Qpt Rpt
    tables rb sb 255 (by norm_num) (n + 3060) hb hb' htab
    (mux4W_soundness_of_ulwc _ _ _ _ _ _ env (n + 3060) hm)
  have hC : ladAcc (goodOffsetAffinePt H hH) Qpt Rpt env.toEnvironment rb sb 255
      = ((-1 : ℤ) ^ 256) • (goodOffsetAffinePt H hH)
        + (bitSum env.toEnvironment rb 255) • Qpt
        + (bitSumT env.toEnvironment sb 255) • Rpt := by
    rw [ladAcc_split, ladAccH_eq, ladAccQ_eq, ladAccR_eq]
  rw [hC] at hval255
  rw [show ((-1 : ℤ) ^ 256) = 1 from by norm_num] at hval255
  have havoid := famOf_avoids_affine env.toEnvironment eb rb sb Qpt Rpt H hH hgood
  have hc4 : (famOf env.toEnvironment eb rb sb Qpt Rpt).toAffine.coeff
      (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
        (⟨255, by norm_num⟩, false))))))) = 4 := by
    simp only [famOf_coeff_apply]
    rfl
  have hc2 : (famOf env.toEnvironment eb rb sb Qpt Rpt).toAffine.coeff
      (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
        (⟨255, by norm_num⟩, true))))))) = 2 := by
    simp only [famOf_coeff_apply]
    rfl
  have hS4 := nsmul_ne_of_slot havoid _ hc4
    (T := sigma 255 • (ladOff env.toEnvironment Qpt Rpt rb sb 255
      + -((rBitAt env.toEnvironment rb 255) • Qpt)
      + -((tBitAt env.toEnvironment sb 255) • Rpt)))
    (famOf_target_ladStep_false env.toEnvironment eb rb sb Qpt Rpt ⟨255, by norm_num⟩)
  have hS2 := nsmul_ne_of_slot havoid _ hc2
    (T := sigma 255 • (-(ladOff env.toEnvironment Qpt Rpt rb sb 255)
      + -((rBitAt env.toEnvironment rb 255) • Qpt)
      + -((tBitAt env.toEnvironment sb 255) • Rpt)))
    (famOf_target_ladStep_true env.toEnvironment eb rb sb Qpt Rpt ⟨255, by norm_num⟩)
  have hs : sigma 255 = -1 := by
    simp only [sigma]
    norm_num
  set B0 : Affine.Point Wp := rBitAt env.toEnvironment rb 255 • Qpt
    + tBitAt env.toEnvironment sb 255 • Rpt with hB0
  set B1 : Affine.Point Wp := bitSum env.toEnvironment rb 255 • Qpt
    + bitSumT env.toEnvironment sb 255 • Rpt with hB1
  have hT : Affine.Point.some _ _ hTm
      = (-3 : ℤ) • goodOffsetAffinePt H hH + B0 := by
    rw [hTval]
    simp only [Tpt, hs, hB0]
    rw [show (3 : ℤ) * (-1) = -3 from by norm_num]
    abel
  have hCv : Affine.Point.some _ _ hns255
      = (1 : ℤ) • goodOffsetAffinePt H hH + B1 := by
    rw [hval255, hB1]
    abel
  have h4 : ((1 : ℤ) - (-3)) • goodOffsetAffinePt H hH ≠ B0 - B1 := by
    have h := hS4
    rw [hs] at h
    simp only [ladOff, neg_one_zsmul] at h
    intro heq
    refine h ?_
    rw [show ((1 : ℤ) - (-3)) = ((4 : Nat) : ℤ) from by norm_num, nsmul_eq_zsmul_int] at heq
    rw [heq]
    simp only [hB0, hB1]
    abel
  have h2 : ((-3 : ℤ) + 1) • goodOffsetAffinePt H hH ≠ -(B0 + B1) := by
    have h := hS2
    rw [hs] at h
    simp only [ladOff, neg_one_zsmul] at h
    intro heq
    refine h ?_
    rw [show ((-3 : ℤ) + 1) = -((2 : Nat) : ℤ) from by decide, neg_zsmul,
      nsmul_eq_zsmul_int] at heq
    rw [neg_inj] at heq
    rw [heq]
    simp only [hB0, hB1]
    abel
  have hne := X_ne_of_avoids_zsmul hTm hns255 (goodOffsetAffinePt H hH) (-3) 1 B0 B1
    hT hCv (by omega) (fun _ => h4) h2
  exact sub_ne_zero.mpr hne

set_option linter.constructorNameAsVariable false in
/-- `hjf2`: the second denominator of the final `elmTo` does not vanish.  The
accumulator is `C₂₅₅ = H + B₁` and the last table entry is `T₂₅₅ = -3·H + B₀`,
so the two bad equations are `T₂₅₅ = O` and `2·C₂₅₅ + T₂₅₅ = O` — the
`ladDbl` slots at `j = 255`. -/
theorem hjf2_dx_of_ulwc (env : ProverEnvironment Fp) (eb : Vector E 256)
    (rb sb : Vector E 256) (Qpt Rpt : Affine.Point Wp) (H : AffinePoint K)
    (hH : H.IsOnCurve params)
    (hgood : GoodOffset H hH (famOf env.toEnvironment eb rb sb Qpt Rpt))
    (acc0 : Pt) (tables : Tables) (target : Pt) (n : Nat)
    (hacc0 : ∃ hns : NS (Expression.eval env.toEnvironment acc0.1)
        (Expression.eval env.toEnvironment acc0.2),
      Affine.Point.some (Expression.eval env.toEnvironment acc0.1)
        (Expression.eval env.toEnvironment acc0.2) hns = -goodOffsetAffinePt H hH)
    (hb : ∀ k : Fin 256,
      Expression.eval env.toEnvironment (rb.get k) = 0 ∨
        Expression.eval env.toEnvironment (rb.get k) = 1)
    (hb' : ∀ k : Fin 256,
      Expression.eval env.toEnvironment (sb.get k) = 0 ∨
        Expression.eval env.toEnvironment (sb.get k) = 1)
    (htab : ∀ (j : Nat) (hj : j < 256) (v w : Fp), (v = 0 ∨ v = 1) → (w = 0 ∨ w = 1) →
      ∃ hns : NS (if v = 0 then
            (if w = 0 then Expression.eval env.toEnvironment (tables.x0 j).1
              else Expression.eval env.toEnvironment (tables.x2 j).1)
          else (if w = 0 then Expression.eval env.toEnvironment (tables.x1 j).1
            else Expression.eval env.toEnvironment (tables.x3 j).1))
          (if v = 0 then
            (if w = 0 then Expression.eval env.toEnvironment (tables.x0 j).2
              else Expression.eval env.toEnvironment (tables.x2 j).2)
          else (if w = 0 then Expression.eval env.toEnvironment (tables.x1 j).2
            else Expression.eval env.toEnvironment (tables.x3 j).2)),
        Affine.Point.some _ _ hns
          = (3 * sigma j) • goodOffsetAffinePt H hH
            + (if v = 1 then (1 : ℤ) else 0) • Qpt
            + (if w = 1 then (1 : ℤ) else 0) • Rpt)
    (hDxf : Expression.eval env.toEnvironment
        ((mux4W (rb.get ⟨0, by omega⟩) (sb.get ⟨0, by omega⟩)
          (tables.x0 255) (tables.x1 255) (tables.x2 255) (tables.x3 255)).output
          (n + 3060)).1
      - Expression.eval env.toEnvironment (jlOut acc0 tables rb sb n).1 ≠ 0)
    (hw : env.UsesLocalWitnessesCompleteness n
      ((jointLadder acc0 tables rb sb target).operations n)) :
    Expression.eval env.toEnvironment (jlOut acc0 tables rb sb n).1
      - env.get (n + 3060 + 6 + 2) ≠ 0 := by
  classical
  obtain ⟨hm, he⟩ := jointLadder_final_ulwc acc0 tables rb sb target env n hw
  obtain ⟨hns255, hval255⟩ :=
    jointLadder_ladInv_255_of_ulwc env n H hH Qpt Rpt eb rb sb acc0 tables target
      hgood hw hacc0 hb hb' htab
  obtain ⟨hTm, hTval⟩ := mux4W_Tpt env.toEnvironment (goodOffsetAffinePt H hH) Qpt Rpt
    tables rb sb 255 (by norm_num) (n + 3060) hb hb' htab
    (mux4W_soundness_of_ulwc _ _ _ _ _ _ env (n + 3060) hm)
  have hC : ladAcc (goodOffsetAffinePt H hH) Qpt Rpt env.toEnvironment rb sb 255
      = ((-1 : ℤ) ^ 256) • (goodOffsetAffinePt H hH)
        + (bitSum env.toEnvironment rb 255) • Qpt
        + (bitSumT env.toEnvironment sb 255) • Rpt := by
    rw [ladAcc_split, ladAccH_eq, ladAccQ_eq, ladAccR_eq]
  rw [hC] at hval255
  rw [show ((-1 : ℤ) ^ 256) = 1 from by norm_num] at hval255
  obtain ⟨hU, hUval⟩ := elmToXu_group_of_ulwc (jlOut acc0 tables rb sb n)
    ((mux4W (rb.get ⟨0, by omega⟩) (sb.get ⟨0, by omega⟩)
      (tables.x0 255) (tables.x1 255) (tables.x2 255) (tables.x3 255)).output (n + 3060))
    target env (n + 3060 + 6) hns255 hTm hDxf he
  have havoid := famOf_avoids_affine env.toEnvironment eb rb sb Qpt Rpt H hH hgood
  have hc3 : (famOf env.toEnvironment eb rb sb Qpt Rpt).toAffine.coeff
      (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (⟨255, by norm_num⟩, true))))))) = 3 := by
    simp only [famOf_coeff_apply]
    rfl
  have hc1 : (famOf env.toEnvironment eb rb sb Qpt Rpt).toAffine.coeff
      (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (⟨255, by norm_num⟩, false))))))) = 1 := by
    simp only [famOf_coeff_apply]
    rfl
  have hS3 := nsmul_ne_of_slot havoid _ hc3
    (T := sigma 255 • (-((rBitAt env.toEnvironment rb 255) • Qpt)
      + -((tBitAt env.toEnvironment sb 255) • Rpt)))
    (famOf_target_ladDbl_true env.toEnvironment eb rb sb Qpt Rpt ⟨255, by norm_num⟩)
  have hS1 := nsmul_ne_of_slot havoid _ hc1
    (T := sigma 255 • ((-2 : ℤ) • (ladOff env.toEnvironment Qpt Rpt rb sb 255)
      + -((rBitAt env.toEnvironment rb 255) • Qpt)
      + -((tBitAt env.toEnvironment sb 255) • Rpt)))
    (famOf_target_ladDbl_false env.toEnvironment eb rb sb Qpt Rpt ⟨255, by norm_num⟩)
  have hs : sigma 255 = -1 := by
    simp only [sigma]
    norm_num
  set B0 : Affine.Point Wp := rBitAt env.toEnvironment rb 255 • Qpt
    + tBitAt env.toEnvironment sb 255 • Rpt with hB0
  set B1 : Affine.Point Wp := bitSum env.toEnvironment rb 255 • Qpt
    + bitSumT env.toEnvironment sb 255 • Rpt with hB1
  have hPpt : Affine.Point.some (Expression.eval env.toEnvironment (jlOut acc0 tables rb sb n).1)
        (Expression.eval env.toEnvironment (jlOut acc0 tables rb sb n).2) hns255
      = (1 : ℤ) • goodOffsetAffinePt H hH + B1 := by
    rw [hval255, hB1]
    abel
  have hQpt : Affine.Point.some (env.get (n + 3060 + 6 + 2))
        (ElmAlgebra.elmMiddleY (Expression.eval env.toEnvironment (jlOut acc0 tables rb sb n).1)
          (Expression.eval env.toEnvironment (jlOut acc0 tables rb sb n).2)
          (env.get (n + 3060 + 6 + 2)) (env.get (n + 3060 + 6 + 1))) hU
      = (-2 : ℤ) • goodOffsetAffinePt H hH + (B0 + B1) := by
    rw [hUval, hTval, hval255]
    simp only [hB0, hB1, Tpt, hs]
    rw [show (3 * -1 : ℤ) = -3 from by norm_num]
    abel
  have h1 : (-2 : ℤ) ≤ 1 → (1 - (-2)) • goodOffsetAffinePt H hH ≠ (B0 + B1) - B1 := by
    intro _
    have h := hS3
    rw [hs] at h
    simp only [neg_one_zsmul] at h
    intro heq
    refine h ?_
    rw [show (1 - (-2) : ℤ) = ((3 : Nat) : ℤ) from by norm_num, nsmul_eq_zsmul_int] at heq
    rw [heq]
    simp only [hB0, hB1]
    abel
  have h3 : (1 + (-2)) • goodOffsetAffinePt H hH ≠ -(B1 + (B0 + B1)) := by
    have h := hS1
    rw [hs] at h
    simp only [neg_one_zsmul, ladOff] at h
    intro heq
    refine h ?_
    rw [show (1 + (-2) : ℤ) = -((1 : Nat) : ℤ) from by norm_num, neg_zsmul,
      nsmul_eq_zsmul_int, neg_inj] at heq
    rw [heq]
    simp only [hB0, hB1]
    abel
  have hne := X_ne_of_avoids_zsmul hns255 hU (goodOffsetAffinePt H hH) 1 (-2) B1 (B0 + B1)
    hPpt hQpt h1 (by omega) h3
  exact sub_ne_zero.mpr hne

/-! ## The `elmTo` rows 1–4, from local witnesses -/

/-- Rows 1–4 of `elmTo`'s `elmCore`, in the `elmEqs` shape. -/
theorem elmTo_rows14_of_ulwc (p q target : Pt) (env : ProverEnvironment Fp) (m : Nat)
    (hDx : Expression.eval env.toEnvironment q.1 - Expression.eval env.toEnvironment p.1 ≠ 0)
    (hDx2 : Expression.eval env.toEnvironment p.1 - env.get (m + 2) ≠ 0)
    (hw : env.UsesLocalWitnessesCompleteness m ((elmTo p q target).operations m)) :
    (Expression.eval env.toEnvironment q.1 - Expression.eval env.toEnvironment p.1)
        * env.get m = 1
      ∧ (Expression.eval env.toEnvironment q.1 - Expression.eval env.toEnvironment p.1)
          * env.get (m + 1)
        = Expression.eval env.toEnvironment q.2 - Expression.eval env.toEnvironment p.2
      ∧ env.get (m + 1) * env.get (m + 1) - Expression.eval env.toEnvironment p.1
          - Expression.eval env.toEnvironment q.1 - env.get (m + 2) = 0
      ∧ (env.get (m + 1) + env.get (m + 3))
          * (Expression.eval env.toEnvironment p.1 - env.get (m + 2))
          - 2 * Expression.eval env.toEnvironment p.2 = 0 := by
  simp only [elmTo, elmCore, nonzero, circuit_norm, pm] at hw
  obtain ⟨r1, r2, r3, r4⟩ := hw
  simp only [eval_cst, eval_sc] at r1 r2 r3 r4
  rw [show m + 1 + 1 + 1 = m + 3 from by omega] at r4
  rw [show m + 1 + 1 = m + 2 from by omega] at r3 r4
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [r1]
    exact mul_inv_cancel₀ hDx
  · rw [r2, r1]
    field_simp
  · rw [r3]
    ring
  · rw [r4]
    field_simp
    ring

/-! ## The ladder's per-step local witnesses -/

set_option linter.constructorNameAsVariable false in
/-- The per-step local witnesses of the ladder, in `mux4W`/`elm` form. -/
theorem jointLadder_step_ulwc (acc0 : Pt) (tables : Tables) (rb sb : Vector E 256)
    (target : Pt) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n
      ((jointLadder acc0 tables rb sb target).operations n)) :
    ∀ (j : Nat) (hj : j < 255),
      env.UsesLocalWitnessesCompleteness (n + j * 12)
          ((mux4W (rb.get ⟨255 - j, by omega⟩) (sb.get ⟨255 - j, by omega⟩)
            (tables.x0 j) (tables.x1 j) (tables.x2 j) (tables.x3 j)).operations
            (n + j * 12))
        ∧ env.UsesLocalWitnessesCompleteness (n + j * 12 + 6)
          ((elm (jlAcc acc0 tables rb sb n ⟨j, hj⟩)
            ((mux4W (rb.get ⟨255 - j, by omega⟩) (sb.get ⟨255 - j, by omega⟩)
              (tables.x0 j) (tables.x1 j) (tables.x2 j) (tables.x3 j)).output
              (n + j * 12))).operations (n + j * 12 + 6)) := by
  rw [jointLadder_ops] at hw
  rw [ulwc_append] at hw
  simp only [jointLadderFold_localLength] at hw
  obtain ⟨hwfold, -⟩ := hw
  rw [Circuit.foldlRange.usesLocalWitnesses] at hwfold
  intro j hj
  have h := hwfold ⟨j, hj⟩
  simp only [jointLadderBody_localLength] at h
  rw [← jlAcc_eq] at h
  rw [jointLadderBody_ops] at h
  rw [ulwc_append] at h
  simp only [mux4W_localLength] at h
  exact h

/-! ## All six ladder fields of `CompleteWitness` -/

set_option linter.constructorNameAsVariable false in
/-- **All six ladder fields of `CompleteWitness`**, discharged from the ladder's
own local witnesses plus a good offset.  No hypothesis mentions the
denominators. -/
theorem jointLadder_denominators_of_ulwc (env : ProverEnvironment Fp) (eb : Vector E 256)
    (rb sb : Vector E 256) (Qpt Rpt : Affine.Point Wp) (H : AffinePoint K)
    (hH : H.IsOnCurve params)
    (hgood : GoodOffset H hH (famOf env.toEnvironment eb rb sb Qpt Rpt))
    (acc0 : Pt) (tables : Tables) (target : Pt) (n : Nat)
    (hacc0 : ∃ hns : NS (Expression.eval env.toEnvironment acc0.1)
        (Expression.eval env.toEnvironment acc0.2),
      Affine.Point.some (Expression.eval env.toEnvironment acc0.1)
        (Expression.eval env.toEnvironment acc0.2) hns = -goodOffsetAffinePt H hH)
    (hb : ∀ k : Fin 256,
      Expression.eval env.toEnvironment (rb.get k) = 0 ∨
        Expression.eval env.toEnvironment (rb.get k) = 1)
    (hb' : ∀ k : Fin 256,
      Expression.eval env.toEnvironment (sb.get k) = 0 ∨
        Expression.eval env.toEnvironment (sb.get k) = 1)
    (htab : ∀ (j : Nat) (hj : j < 256) (v w : Fp), (v = 0 ∨ v = 1) → (w = 0 ∨ w = 1) →
      ∃ hns : NS (if v = 0 then
            (if w = 0 then Expression.eval env.toEnvironment (tables.x0 j).1
              else Expression.eval env.toEnvironment (tables.x2 j).1)
          else (if w = 0 then Expression.eval env.toEnvironment (tables.x1 j).1
            else Expression.eval env.toEnvironment (tables.x3 j).1))
          (if v = 0 then
            (if w = 0 then Expression.eval env.toEnvironment (tables.x0 j).2
              else Expression.eval env.toEnvironment (tables.x2 j).2)
          else (if w = 0 then Expression.eval env.toEnvironment (tables.x1 j).2
            else Expression.eval env.toEnvironment (tables.x3 j).2)),
        Affine.Point.some _ _ hns
          = (3 * sigma j) • goodOffsetAffinePt H hH
            + (if v = 1 then (1 : ℤ) else 0) • Qpt
            + (if w = 1 then (1 : ℤ) else 0) • Rpt)
    (hw : env.UsesLocalWitnessesCompleteness n
      ((jointLadder acc0 tables rb sb target).operations n))
    {r s : K} (Ed : Nat) (Q : AffinePoint K) (hQ : Q.IsOnCurve params)
    (hQns : NS Q.X Q.Y)
    (hRns : NS (affinePt (stdV Q r s Ed)).X (affinePt (stdV Q r s Ed)).Y)
    (hQpt : Qpt = Affine.Point.some Q.X Q.Y hQns)
    (hRpt : Rpt = Affine.Point.some (affinePt (stdV Q r s Ed)).X
      (affinePt (stdV Q r s Ed)).Y hRns)
    (ep : Affine.Point Wp)
    (hTgt : NS (Expression.eval env.toEnvironment target.1)
      (Expression.eval env.toEnvironment target.2))
    (hep : ep = goodOffsetAffinePt H hH + Ed • Projective.Point.toAffineLift Gpt)
    (hneg : Affine.Point.some (Expression.eval env.toEnvironment target.1)
        (Expression.eval env.toEnvironment target.2) hTgt = -ep)
    (hs0 : 0 < s.val) (hsn : s.val < StandardECDSA.n)
    (hVne : ¬ ProjectiveEquiv (stdV Q r s Ed) infinityPoint)
    (hr : (leNat (fun k : Fin 256 =>
      (Expression.eval env.toEnvironment (rb.get k)).val) : ℤ) = r.val)
    (ht : (leNat (fun k : Fin 256 =>
      (Expression.eval env.toEnvironment (sb.get k)).val) : ℤ) = ((StandardECDSA.n - s.val : Nat) : ℤ)) :
    (∀ j : Fin 255, Expression.eval env.toEnvironment
        ((mux4W (rb.get ⟨255 - j.val, by omega⟩) (sb.get ⟨255 - j.val, by omega⟩)
          (tables.x0 j.val) (tables.x1 j.val) (tables.x2 j.val)
          (tables.x3 j.val)).output (n + j.val * 12)).1
      - Expression.eval env.toEnvironment (jlAcc acc0 tables rb sb n j).1 ≠ 0)
    ∧ (∀ j : Fin 255, Expression.eval env.toEnvironment (jlAcc acc0 tables rb sb n j).1
      - env.get (n + j.val * 12 + 6 + 2) ≠ 0)
    ∧ (Expression.eval env.toEnvironment
        ((mux4W (rb.get ⟨0, by omega⟩) (sb.get ⟨0, by omega⟩)
          (tables.x0 255) (tables.x1 255) (tables.x2 255) (tables.x3 255)).output
          (n + 3060)).1
      - Expression.eval env.toEnvironment (jlOut acc0 tables rb sb n).1 ≠ 0)
    ∧ (Expression.eval env.toEnvironment (jlOut acc0 tables rb sb n).1
      - env.get (n + 3060 + 6 + 2) ≠ 0)
    ∧ (env.get (n + 3060 + 6 + 3) * env.get (n + 3060 + 6 + 3)
      - Expression.eval env.toEnvironment (jlOut acc0 tables rb sb n).1
      - env.get (n + 3060 + 6 + 2) - Expression.eval env.toEnvironment target.1 = 0)
    ∧ (env.get (n + 3060 + 6 + 3)
        * (Expression.eval env.toEnvironment (jlOut acc0 tables rb sb n).1
          - Expression.eval env.toEnvironment target.1)
      - Expression.eval env.toEnvironment (jlOut acc0 tables rb sb n).2
      - Expression.eval env.toEnvironment target.2 = 0) := by
  classical
  have hacc := jointLadder_ladInv_of_ulwc env n H hH Qpt Rpt eb rb sb acc0 tables target
    hgood hw hacc0 hb hb' htab
  have hstep := jointLadder_step_ulwc acc0 tables rb sb target env n hw
  have hDx : ∀ j : Fin 255, Expression.eval env.toEnvironment
      ((mux4W (rb.get ⟨255 - j.val, by omega⟩) (sb.get ⟨255 - j.val, by omega⟩)
        (tables.x0 j.val) (tables.x1 j.val) (tables.x2 j.val)
        (tables.x3 j.val)).output (n + j.val * 12)).1
      - Expression.eval env.toEnvironment (jlAcc acc0 tables rb sb n j).1 ≠ 0 := by
    intro j
    exact hj1_dx_of_ladInv env.toEnvironment eb rb sb Qpt Rpt H hH hgood tables n
      hb hb' htab j.val j.isLt _
      (mux4W_soundness_of_ulwc _ _ _ _ _ _ env (n + j.val * 12) (hstep j.val j.isLt).1)
      (hacc j)
  have hDx2 : ∀ j : Fin 255, Expression.eval env.toEnvironment (jlAcc acc0 tables rb sb n j).1
      - env.get (n + j.val * 12 + 6 + 2) ≠ 0 := by
    intro j
    have hm := mux4W_soundness_of_ulwc _ _ _ _ _ _ env (n + j.val * 12)
      (hstep j.val j.isLt).1
    have hrows := elm_rows123_of_ulwc _ _ env (n + j.val * 12 + 6)
      (hstep j.val j.isLt).2 (hDx j)
    exact hj2_dx_of_ladInv env.toEnvironment eb rb sb Qpt Rpt H hH hgood tables n
      hb hb' htab j.val j.isLt _ hm (hDx j) hrows.1 hrows.2 (hacc j)
  have hDxf := hjf1_dx_of_ulwc env eb rb sb Qpt Rpt H hH hgood acc0 tables target n
    hacc0 hb hb' htab hw
  have hDx2f := hjf2_dx_of_ulwc env eb rb sb Qpt Rpt H hH hgood acc0 tables target n
    hacc0 hb hb' htab hDxf hw
  obtain ⟨hns255, hval255⟩ :=
    jointLadder_ladInv_255_of_ulwc env n H hH Qpt Rpt eb rb sb acc0 tables target
      hgood hw hacc0 hb hb' htab
  obtain ⟨hm, he⟩ := jointLadder_final_ulwc acc0 tables rb sb target env n hw
  obtain ⟨hTm, hTval⟩ := mux4W_Tpt env.toEnvironment (goodOffsetAffinePt H hH) Qpt Rpt
    tables rb sb 255 (by norm_num) (n + 3060) hb hb' htab
    (mux4W_soundness_of_ulwc _ _ _ _ _ _ env (n + 3060) hm)
  have htarget256 := ladAcc_256_eq_target env Ed H hH Qpt Rpt rb sb Q hQ hQns hRns hQpt hRpt
    target ep hTgt hep hneg hs0 hsn hVne hb hb' hr ht
  have hgrp : 2 • Affine.Point.some
        (Expression.eval env.toEnvironment (jlOut acc0 tables rb sb n).1)
        (Expression.eval env.toEnvironment (jlOut acc0 tables rb sb n).2) hns255
      + Affine.Point.some (Expression.eval env.toEnvironment
          ((mux4W (rb.get ⟨0, by omega⟩) (sb.get ⟨0, by omega⟩)
            (tables.x0 255) (tables.x1 255) (tables.x2 255) (tables.x3 255)).output
            (n + 3060)).1)
          (Expression.eval env.toEnvironment
          ((mux4W (rb.get ⟨0, by omega⟩) (sb.get ⟨0, by omega⟩)
            (tables.x0 255) (tables.x1 255) (tables.x2 255) (tables.x3 255)).output
            (n + 3060)).2) hTm
      = Affine.Point.some (Expression.eval env.toEnvironment target.1)
          (Expression.eval env.toEnvironment target.2) hTgt := by
    rw [hval255, hTval, ← htarget256]
    rfl
  obtain ⟨e1, e2, e3, e4⟩ := elmTo_rows14_of_ulwc (jlOut acc0 tables rb sb n)
    ((mux4W (rb.get ⟨0, by omega⟩) (sb.get ⟨0, by omega⟩)
      (tables.x0 255) (tables.x1 255) (tables.x2 255) (tables.x3 255)).output (n + 3060))
    target env (n + 3060 + 6) hDxf hDx2f he
  obtain ⟨h1f, h2f⟩ := elmTo_rows_of_group env.toEnvironment
    (jlOut acc0 tables rb sb n)
    ((mux4W (rb.get ⟨0, by omega⟩) (sb.get ⟨0, by omega⟩)
      (tables.x0 255) (tables.x1 255) (tables.x2 255) (tables.x3 255)).output (n + 3060))
    target (n + 3060 + 6) hns255 hTm hTgt hgrp e1 e2 e3 e4
  have hc := jointLadder_soundness_of_ulwc acc0 tables rb sb target env n hw
    hDx hDx2 hDxf hDx2f h1f h2f
  exact jointLadder_denominators env.toEnvironment eb rb sb Qpt Rpt H hH hgood acc0 tables
    target n hacc0 hb hb' htab hc

end StandardECDSA
