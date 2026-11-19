/-
# Honest-witness denominators (task G2-b, ladder part) — the joint induction

`hj1_dx` and `hj2_dx` (`HonestLadder.lean`) read the mux/elm soundness and the
accumulator's group image off the *phase's* soundness `hc`.  That makes them
unusable for discharging the denominators, because `hc` itself needs them.

The two lemmas below take those two ingredients directly instead, which is what
lets `jointLadder_ladInv_of_ulwc` run the joint induction
`ladInv j -> hDx j -> body soundness j -> ladInv (j+1)`.

Every proof is complete; no new axioms and no `native_decide`.
-/

import StandardECDSA.HonestLadder
import StandardECDSA.Phases.HonestLadderPhase

namespace StandardECDSA

open WeierstrassCurve StandardECDSA StandardECDSA.Gadgets StandardECDSA.Phases
  StandardECDSA.Math
open StandardECDSA.Math.FixedTables

/-! ## The two per-step denominators, from the prefix invariant -/

theorem elmXu_group_of_rows (env : Environment Fp) (p q : Pt) (m : Nat)
    (hA : NS (Expression.eval env p.1) (Expression.eval env p.2))
    (hB : NS (Expression.eval env q.1) (Expression.eval env q.2))
    (hDx : Expression.eval env q.1 - Expression.eval env p.1 ≠ 0)
    (h1 : env.get (m + 1) * (Expression.eval env q.1 - Expression.eval env p.1)
      = Expression.eval env q.2 - Expression.eval env p.2)
    (h2 : env.get (m + 1) * env.get (m + 1)
      = Expression.eval env p.1 + Expression.eval env q.1 + env.get (m + 2)) :
    ∃ hU : NS (env.get (m + 2))
        (ElmAlgebra.elmMiddleY (Expression.eval env p.1) (Expression.eval env p.2)
          (env.get (m + 2)) (env.get (m + 1))),
      Affine.Point.some (env.get (m + 2))
          (ElmAlgebra.elmMiddleY (Expression.eval env p.1) (Expression.eval env p.2)
            (env.get (m + 2)) (env.get (m + 1))) hU
        = Affine.Point.some (Expression.eval env p.1) (Expression.eval env p.2) hA
          + Affine.Point.some (Expression.eval env q.1) (Expression.eval env q.2) hB := by
  have hYU : env.get (m + 1) * (Expression.eval env p.1 - env.get (m + 2))
      = Expression.eval env p.2
        + ElmAlgebra.elmMiddleY (Expression.eval env p.1) (Expression.eval env p.2)
            (env.get (m + 2)) (env.get (m + 1)) := by
    simp only [ElmAlgebra.elmMiddleY]
    ring
  have hU := ElmAlgebra.affine_add_onCurve params.a params.b
    (Expression.eval env p.1) (Expression.eval env p.2)
    (Expression.eval env q.1) (Expression.eval env q.2)
    (env.get (m + 2))
    (ElmAlgebra.elmMiddleY (Expression.eval env p.1) (Expression.eval env p.2)
      (env.get (m + 2)) (env.get (m + 1)))
    (env.get (m + 1)) (ns_equation _ _ hA) (ns_equation _ _ hB) hDx h1 h2 hYU
  refine ⟨Math.AffineBridge.short_nonsingular params _ _ hU, ?_⟩
  exact Math.AffineBridge.affine_add_eq_group params
    (Expression.eval env p.1) (Expression.eval env p.2)
    (Expression.eval env q.1) (Expression.eval env q.2)
    (env.get (m + 2))
    (ElmAlgebra.elmMiddleY (Expression.eval env p.1) (Expression.eval env p.2)
      (env.get (m + 2)) (env.get (m + 1)))
    (env.get (m + 1))
    (Math.AffineBridge.short_nonsingular params _ _ (ns_equation _ _ hA))
    (Math.AffineBridge.short_nonsingular params _ _ (ns_equation _ _ hB))
    (Math.AffineBridge.short_nonsingular params _ _ hU) hDx h1 h2 hYU

/-- Rows 2 and 3 of `elmCore`, from the local witnesses.  These are the only
rows `elmXu_group_of_rows` needs, and unlike row 4 they do **not** require the
second denominator — which is what breaks the `hDx2 <-> row 4` circularity. -/
theorem elm_rows123_of_ulwc (p q : Pt) (env : ProverEnvironment Fp) (m : Nat)
    (hw : env.UsesLocalWitnessesCompleteness m ((elm p q).operations m))
    (hDx : Expression.eval env.toEnvironment q.1 - Expression.eval env.toEnvironment p.1 ≠ 0) :
    env.get (m + 1) * (Expression.eval env.toEnvironment q.1
        - Expression.eval env.toEnvironment p.1)
      = Expression.eval env.toEnvironment q.2 - Expression.eval env.toEnvironment p.2 ∧
    env.get (m + 1) * env.get (m + 1)
      = Expression.eval env.toEnvironment p.1 + Expression.eval env.toEnvironment q.1
        + env.get (m + 2) := by
  simp only [elm, elmCore, nonzero, circuit_norm, pm] at hw
  obtain ⟨e1, e2, e3, e4, -, -⟩ := hw
  refine ⟨?_, ?_⟩
  · rw [e2, e1]; field_simp
  · linear_combination -e3

set_option linter.constructorNameAsVariable false in
/-- **The first ladder denominator does not vanish**, from the prefix invariant.

Same slot argument as `hj1_dx`, but the mux soundness and the accumulator's
group image are supplied directly instead of being read off the phase's
soundness — which is what lets the joint induction run. -/
theorem hj1_dx_of_ladInv (env : Environment Fp) (eb : Vector E 256) (rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) (H : AffinePoint K) (hH : H.IsOnCurve params)
    (hgood : GoodOffset H hH (famOf env eb rb sb Qpt Rpt))
    (tables : Tables) (n : Nat)
    (hb : ∀ k : Fin 256, Expression.eval env (rb.get k) = 0 ∨ Expression.eval env (rb.get k) = 1)
    (hb' : ∀ k : Fin 256, Expression.eval env (sb.get k) = 0 ∨ Expression.eval env (sb.get k) = 1)
    (htab : ∀ (j : Nat) (hj : j < 256) (v w : Fp), (v = 0 ∨ v = 1) → (w = 0 ∨ w = 1) →
      ∃ hns : NS (if v = 0 then
            (if w = 0 then Expression.eval env (tables.x0 j).1
              else Expression.eval env (tables.x2 j).1)
          else (if w = 0 then Expression.eval env (tables.x1 j).1
            else Expression.eval env (tables.x3 j).1))
          (if v = 0 then
            (if w = 0 then Expression.eval env (tables.x0 j).2
              else Expression.eval env (tables.x2 j).2)
          else (if w = 0 then Expression.eval env (tables.x1 j).2
            else Expression.eval env (tables.x3 j).2)),
        Affine.Point.some _ _ hns
          = (3 * sigma j) • goodOffsetAffinePt H hH
            + (if v = 1 then (1 : ℤ) else 0) • Qpt
            + (if w = 1 then (1 : ℤ) else 0) • Rpt)
    (j : Nat) (hj : j < 255) (acc : Pt)
    (hm : ConstraintsHold.Soundness env
      ((mux4W (rb.get ⟨255 - j, by omega⟩) (sb.get ⟨255 - j, by omega⟩)
        (tables.x0 j) (tables.x1 j) (tables.x2 j) (tables.x3 j)).operations (n + j * 12)))
    (hacc : ladInv (goodOffsetAffinePt H hH) Qpt Rpt env rb sb j acc) :
    Expression.eval env
        ((mux4W (rb.get ⟨255 - j, by omega⟩) (sb.get ⟨255 - j, by omega⟩)
          (tables.x0 j) (tables.x1 j) (tables.x2 j) (tables.x3 j)).output (n + j * 12)).1
      - Expression.eval env acc.1 ≠ 0 := by
  classical
  obtain ⟨hTm, hTval⟩ :=
    mux4W_Tpt env (goodOffsetAffinePt H hH) Qpt Rpt tables rb sb j (by omega) (n + j * 12)
      hb hb' htab hm
  obtain ⟨hns, hval⟩ := hacc
  have hC : ladAcc (goodOffsetAffinePt H hH) Qpt Rpt env rb sb j
      = ((-1 : ℤ) ^ (j + 1)) • (goodOffsetAffinePt H hH)
        + (bitSum env rb j) • Qpt + (bitSumT env sb j) • Rpt := by
    rw [ladAcc_split, ladAccH_eq, ladAccQ_eq, ladAccR_eq]
  rw [hC] at hval
  have havoid := famOf_avoids_affine env eb rb sb Qpt Rpt H hH hgood
  have hc4 : (famOf env eb rb sb Qpt Rpt).toAffine.coeff
      (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (⟨j, by omega⟩, false))))))) = 4 := by
    simp only [famOf_coeff_apply]
    rfl
  have hc2 : (famOf env eb rb sb Qpt Rpt).toAffine.coeff
      (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (⟨j, by omega⟩, true))))))) = 2 := by
    simp only [famOf_coeff_apply]
    rfl
  have hS4 := nsmul_ne_of_slot havoid _ hc4
    (T := sigma j • (ladOff env Qpt Rpt rb sb j
      + -((rBitAt env rb j) • Qpt) + -((tBitAt env sb j) • Rpt)))
    (famOf_target_ladStep_false env eb rb sb Qpt Rpt ⟨j, by omega⟩)
  have hS2 := nsmul_ne_of_slot havoid _ hc2
    (T := sigma j • (-(ladOff env Qpt Rpt rb sb j)
      + -((rBitAt env rb j) • Qpt) + -((tBitAt env sb j) • Rpt)))
    (famOf_target_ladStep_true env eb rb sb Qpt Rpt ⟨j, by omega⟩)
  have hsig : sigma j = 1 ∨ sigma j = -1 := by
    rcases Nat.even_or_odd j with he | ho
    · exact Or.inl (he.neg_one_pow)
    · exact Or.inr (ho.neg_one_pow)
  have hsig' : ((-1 : ℤ) ^ (j + 1)) = -sigma j := by
    rw [pow_succ, sigma]
    ring
  rw [hsig'] at hval
  -- the two `Q`/`R` parts, as named points
  set B0 : Affine.Point Wp := rBitAt env rb j • Qpt + tBitAt env sb j • Rpt with hB0
  set B1 : Affine.Point Wp := bitSum env rb j • Qpt + bitSumT env sb j • Rpt with hB1
  rcases hsig with hs | hs
  · -- `σ_j = 1`: `a = 3`, `b = -1`
    have hT : Affine.Point.some _ _ hTm
        = (3 : ℤ) • goodOffsetAffinePt H hH + B0 := by
      rw [hTval]
      simp only [Tpt, hs, hB0]
      rw [show (3 : ℤ) * 1 = 3 from by norm_num]
      abel
    have hCv : Affine.Point.some _ _ hns
        = (-1 : ℤ) • goodOffsetAffinePt H hH + B1 := by
      rw [hval, hs, hB1]
      abel
    have h4 : ((3 : ℤ) - (-1)) • goodOffsetAffinePt H hH ≠ B1 - B0 := by
      have h := hS4
      rw [hs] at h
      simp only [ladOff, one_zsmul] at h
      intro heq
      refine h ?_
      rw [show ((3 : ℤ) - (-1)) = ((4 : Nat) : ℤ) from by norm_num, nsmul_eq_zsmul_int] at heq
      rw [heq]
      simp only [hB0, hB1]
      abel
    have h2 : ((3 : ℤ) + (-1)) • goodOffsetAffinePt H hH ≠ -(B0 + B1) := by
      have h := hS2
      rw [hs] at h
      simp only [ladOff, one_zsmul] at h
      intro heq
      refine h ?_
      rw [show ((3 : ℤ) + (-1)) = ((2 : Nat) : ℤ) from by norm_num, nsmul_eq_zsmul_int] at heq
      rw [heq]
      simp only [hB0, hB1]
      abel
    have hne := X_ne_of_avoids_zsmul hTm hns (goodOffsetAffinePt H hH) 3 (-1) B0 B1
      hT hCv (fun _ => h4) (by omega) h2
    exact sub_ne_zero.mpr hne
  · -- `σ_j = -1`: `a = -3`, `b = 1`
    have hT : Affine.Point.some _ _ hTm
        = (-3 : ℤ) • goodOffsetAffinePt H hH + B0 := by
      rw [hTval]
      simp only [Tpt, hs, hB0]
      rw [show (3 : ℤ) * (-1) = -3 from by norm_num]
      abel
    have hCv : Affine.Point.some _ _ hns
        = (1 : ℤ) • goodOffsetAffinePt H hH + B1 := by
      rw [hval, hs, hB1]
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
    have hne := X_ne_of_avoids_zsmul hTm hns (goodOffsetAffinePt H hH) (-3) 1 B0 B1
      hT hCv (by omega) (fun _ => h4) h2
    exact sub_ne_zero.mpr hne

set_option linter.constructorNameAsVariable false in
/-- **The second ladder denominator does not vanish**, from the prefix invariant. -/
theorem hj2_dx_of_ladInv (env : Environment Fp) (eb : Vector E 256) (rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) (H : AffinePoint K) (hH : H.IsOnCurve params)
    (hgood : GoodOffset H hH (famOf env eb rb sb Qpt Rpt))
    (tables : Tables) (n : Nat)
    (hb : ∀ k : Fin 256, Expression.eval env (rb.get k) = 0 ∨ Expression.eval env (rb.get k) = 1)
    (hb' : ∀ k : Fin 256, Expression.eval env (sb.get k) = 0 ∨ Expression.eval env (sb.get k) = 1)
    (htab : ∀ (j : Nat) (hj : j < 256) (v w : Fp), (v = 0 ∨ v = 1) → (w = 0 ∨ w = 1) →
      ∃ hns : NS (if v = 0 then
            (if w = 0 then Expression.eval env (tables.x0 j).1
              else Expression.eval env (tables.x2 j).1)
          else (if w = 0 then Expression.eval env (tables.x1 j).1
            else Expression.eval env (tables.x3 j).1))
          (if v = 0 then
            (if w = 0 then Expression.eval env (tables.x0 j).2
              else Expression.eval env (tables.x2 j).2)
          else (if w = 0 then Expression.eval env (tables.x1 j).2
            else Expression.eval env (tables.x3 j).2)),
        Affine.Point.some _ _ hns
          = (3 * sigma j) • goodOffsetAffinePt H hH
            + (if v = 1 then (1 : ℤ) else 0) • Qpt
            + (if w = 1 then (1 : ℤ) else 0) • Rpt)
    (j : Nat) (hj : j < 255) (acc : Pt)
    (hm : ConstraintsHold.Soundness env
      ((mux4W (rb.get ⟨255 - j, by omega⟩) (sb.get ⟨255 - j, by omega⟩)
        (tables.x0 j) (tables.x1 j) (tables.x2 j) (tables.x3 j)).operations (n + j * 12)))
    (hDx : Expression.eval env
        ((mux4W (rb.get ⟨255 - j, by omega⟩) (sb.get ⟨255 - j, by omega⟩)
          (tables.x0 j) (tables.x1 j) (tables.x2 j) (tables.x3 j)).output (n + j * 12)).1
      - Expression.eval env acc.1 ≠ 0)
    (h1 : env.get (n + j * 12 + 6 + 1) * (Expression.eval env
        ((mux4W (rb.get ⟨255 - j, by omega⟩) (sb.get ⟨255 - j, by omega⟩)
          (tables.x0 j) (tables.x1 j) (tables.x2 j) (tables.x3 j)).output (n + j * 12)).1
        - Expression.eval env acc.1)
      = Expression.eval env
          ((mux4W (rb.get ⟨255 - j, by omega⟩) (sb.get ⟨255 - j, by omega⟩)
            (tables.x0 j) (tables.x1 j) (tables.x2 j) (tables.x3 j)).output (n + j * 12)).2
        - Expression.eval env acc.2)
    (h2 : env.get (n + j * 12 + 6 + 1) * env.get (n + j * 12 + 6 + 1)
      = Expression.eval env acc.1
        + Expression.eval env
            ((mux4W (rb.get ⟨255 - j, by omega⟩) (sb.get ⟨255 - j, by omega⟩)
              (tables.x0 j) (tables.x1 j) (tables.x2 j) (tables.x3 j)).output (n + j * 12)).1
        + env.get (n + j * 12 + 6 + 2))
    (hacc : ladInv (goodOffsetAffinePt H hH) Qpt Rpt env rb sb j acc) :
    Expression.eval env acc.1 - env.get (n + j * 12 + 6 + 2) ≠ 0 := by
  classical
  obtain ⟨hTm, hTval⟩ :=
    mux4W_Tpt env (goodOffsetAffinePt H hH) Qpt Rpt tables rb sb j (by omega) (n + j * 12)
      hb hb' htab hm
  obtain ⟨hns, hval⟩ := hacc
  have hC : ladAcc (goodOffsetAffinePt H hH) Qpt Rpt env rb sb j
      = ((-1 : ℤ) ^ (j + 1)) • (goodOffsetAffinePt H hH)
        + (bitSum env rb j) • Qpt + (bitSumT env sb j) • Rpt := by
    rw [ladAcc_split, ladAccH_eq, ladAccQ_eq, ladAccR_eq]
  rw [hC] at hval
  have hXU := elmXu_group_of_rows env acc
    ((mux4W (rb.get ⟨255 - j, by omega⟩) (sb.get ⟨255 - j, by omega⟩)
      (tables.x0 j) (tables.x1 j) (tables.x2 j) (tables.x3 j)).output (n + j * 12))
    (n + j * 12 + 6) hns hTm hDx h1 h2
  obtain ⟨hU, hUval⟩ := hXU
  have havoid := famOf_avoids_affine env eb rb sb Qpt Rpt H hH hgood
  have hc3 : (famOf env eb rb sb Qpt Rpt).toAffine.coeff
      (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (⟨j, by omega⟩, true))))))) = 3 := by
    simp only [famOf_coeff_apply]
    rfl
  have hc1 : (famOf env eb rb sb Qpt Rpt).toAffine.coeff
      (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (⟨j, by omega⟩, false))))))) = 1 := by
    simp only [famOf_coeff_apply]
    rfl
  have hS3 := nsmul_ne_of_slot havoid _ hc3
    (T := sigma j • (-((rBitAt env rb j) • Qpt) + -((tBitAt env sb j) • Rpt)))
    (famOf_target_ladDbl_true env eb rb sb Qpt Rpt ⟨j, by omega⟩)
  have hS1 := nsmul_ne_of_slot havoid _ hc1
    (T := sigma j • ((-2 : ℤ) • (ladOff env Qpt Rpt rb sb j)
      + -((rBitAt env rb j) • Qpt) + -((tBitAt env sb j) • Rpt)))
    (famOf_target_ladDbl_false env eb rb sb Qpt Rpt ⟨j, by omega⟩)
  have hsig : sigma j = 1 ∨ sigma j = -1 := by
    rcases Nat.even_or_odd j with he | ho
    · exact Or.inl (he.neg_one_pow)
    · exact Or.inr (ho.neg_one_pow)
  have hsig' : ((-1 : ℤ) ^ (j + 1)) = -sigma j := by
    rw [pow_succ, sigma]
    ring
  rw [hsig'] at hval
  set B0 : Affine.Point Wp := rBitAt env rb j • Qpt + tBitAt env sb j • Rpt with hB0
  set B1 : Affine.Point Wp := bitSum env rb j • Qpt + bitSumT env sb j • Rpt with hB1
  have hPpt : Affine.Point.some (Expression.eval env (acc).1)
        (Expression.eval env (acc).2) hns
      = (-sigma j) • goodOffsetAffinePt H hH + B1 := by
    rw [hval, hB1]
    abel
  have hQpt : Affine.Point.some (env.get (n + j * 12 + 6 + 2))
        (ElmAlgebra.elmMiddleY (Expression.eval env (acc).1)
          (Expression.eval env (acc).2)
          (env.get (n + j * 12 + 6 + 2)) (env.get (n + j * 12 + 6 + 1))) hU
      = (2 * sigma j) • goodOffsetAffinePt H hH + (B0 + B1) := by
    rw [hUval, hTval, hval]
    simp only [hB0, hB1, Tpt]
    rw [show (2 * sigma j : ℤ) = -sigma j + 3 * sigma j from by ring, add_zsmul]
    abel
  rcases hsig with hs | hs
  · -- `σ_j = 1`: `a = -1`, `b = 2`
    rw [hs] at hPpt hQpt
    have h2 : (-1 : ℤ) ≤ 2 → (2 - (-1)) • goodOffsetAffinePt H hH ≠ B1 - (B0 + B1) := by
      intro _
      have h := hS3
      rw [hs] at h
      simp only [one_zsmul] at h
      intro heq
      refine h ?_
      rw [show (2 - (-1) : ℤ) = ((3 : Nat) : ℤ) from by norm_num, nsmul_eq_zsmul_int] at heq
      rw [heq]
      simp only [hB0, hB1]
      abel
    have h3 : (-1 + 2) • goodOffsetAffinePt H hH ≠ -(B1 + (B0 + B1)) := by
      have h := hS1
      rw [hs] at h
      simp only [one_zsmul, ladOff] at h
      intro heq
      refine h ?_
      rw [show (-1 + 2 : ℤ) = ((1 : Nat) : ℤ) from by norm_num, nsmul_eq_zsmul_int] at heq
      rw [heq]
      simp only [hB0, hB1]
      abel
    have hne := X_ne_of_avoids_zsmul hns hU (goodOffsetAffinePt H hH) (-1) 2 B1 (B0 + B1)
      hPpt hQpt (by omega) h2 h3
    exact sub_ne_zero.mpr hne
  · -- `σ_j = -1`: `a = 1`, `b = -2`
    rw [hs] at hPpt hQpt
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
    have hne := X_ne_of_avoids_zsmul hns hU (goodOffsetAffinePt H hH) 1 (-2) B1 (B0 + B1)
      hPpt hQpt h1 (by omega) h3
    exact sub_ne_zero.mpr hne

/-! ## One ladder step preserves the prefix invariant -/

set_option linter.constructorNameAsVariable false in
/-- One returning ladder step preserves the prefix invariant, given the step's
own rows.  This is the `hstep` of `jointLadder_ladInv`, factored out so the
joint induction can supply the rows itself. -/
theorem jointLadderBody_ladInv_step (env : Environment Fp) (Hpt Qpt Rpt : Affine.Point Wp)
    (tables : Tables) (rb sb : Vector E 256) (n j : Nat) (hj : j < 255) (acc : Pt)
    (hb : ∀ k : Fin 256, Expression.eval env (rb.get k) = 0 ∨ Expression.eval env (rb.get k) = 1)
    (hb' : ∀ k : Fin 256, Expression.eval env (sb.get k) = 0 ∨ Expression.eval env (sb.get k) = 1)
    (htab : ∀ (j : Nat) (hj : j < 256) (v w : Fp), (v = 0 ∨ v = 1) → (w = 0 ∨ w = 1) →
      ∃ hns : NS (if v = 0 then
            (if w = 0 then Expression.eval env (tables.x0 j).1
              else Expression.eval env (tables.x2 j).1)
          else (if w = 0 then Expression.eval env (tables.x1 j).1
            else Expression.eval env (tables.x3 j).1))
          (if v = 0 then
            (if w = 0 then Expression.eval env (tables.x0 j).2
              else Expression.eval env (tables.x2 j).2)
          else (if w = 0 then Expression.eval env (tables.x1 j).2
            else Expression.eval env (tables.x3 j).2)),
        Affine.Point.some _ _ hns
          = (3 * sigma j) • Hpt + (if v = 1 then (1 : ℤ) else 0) • Qpt
            + (if w = 1 then (1 : ℤ) else 0) • Rpt)
    (hacc : ladInv Hpt Qpt Rpt env rb sb j acc)
    (hc : ConstraintsHold.Soundness env
      ((jointLadderBody tables rb sb acc ⟨j, hj⟩).operations (n + j * 12))) :
    ladInv Hpt Qpt Rpt env rb sb (j + 1)
      ((jointLadderBody tables rb sb acc ⟨j, hj⟩).output (n + j * 12)) := by
  obtain ⟨hns, hval⟩ := hacc
  simp only [jointLadderBody_ops, ConstraintsHold.Soundness] at hc
  rw [Operations.forAllNoOffset_append] at hc
  obtain ⟨hm, he⟩ := hc
  obtain ⟨hTm, hTval⟩ :=
    mux4W_Tpt env Hpt Qpt Rpt tables rb sb j (by omega : j < 256) (n + j * 12)
      hb hb' htab hm
  rw [jointLadderBody_out]
  simp only [ladInv]
  obtain ⟨hR, hRval⟩ := elm_sound env _ _ (n + j * 12 + 6) hns hTm he
  refine ⟨hR, ?_⟩
  refine hRval.trans ?_
  rw [hTval, hval]
  simp only [ladAcc]
  rw [two_nsmul, two_zsmul]

/-! ## The joint induction -/

set_option linter.constructorNameAsVariable false in
/-- **The ladder prefix invariant at every step, from the rows.**

The ladder analogue of `fixedBase_fbInv_of_ulwc`: at step `j` the invariant
supplies the group image that `hj1_dx_of_ladInv` and `hj2_dx_of_ladInv` need,
and those supply the two denominators that the step's soundness needs.  The
second denominator is obtained from rows 2 and 3 of `elmCore` (via
`elm_rows123_of_ulwc` + `hj2_dx_of_ladInv`), never from row 4 — which is
what breaks the `hDx2 <-> row 4` circularity. -/
theorem jointLadder_ladInv_of_ulwc (env : ProverEnvironment Fp) (n : Nat)
    (H : AffinePoint K) (hH : H.IsOnCurve params) (Qpt Rpt : Affine.Point Wp)
    (eb rb sb : Vector E 256) (acc0 : Pt) (tables : Tables) (target : Pt)
    (hgood : GoodOffset H hH (famOf env.toEnvironment eb rb sb Qpt Rpt))
    (hw : env.UsesLocalWitnessesCompleteness n
      ((jointLadder acc0 tables rb sb target).operations n))
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
            + (if w = 1 then (1 : ℤ) else 0) • Rpt) :
    ∀ j : Fin 255,
      ladInv (goodOffsetAffinePt H hH) Qpt Rpt env.toEnvironment rb sb j.val
        (jlAcc acc0 tables rb sb n j) := by
  rw [jointLadder_ops] at hw
  rw [ulwc_append] at hw
  simp only [jointLadderFold_localLength] at hw
  obtain ⟨hwfold, -⟩ := hw
  rw [Circuit.foldlRange.usesLocalWitnesses] at hwfold
  have hwin : ∀ (j : Nat) (hj : j < 255),
      env.UsesLocalWitnessesCompleteness (n + j * 12)
        ((jointLadderBody tables rb sb
          (Fin.foldl j (fun acc (i : Fin j) =>
            (jointLadderBody tables rb sb acc ⟨i.val, by omega⟩).output (n + i.val * 12))
            acc0) ⟨j, hj⟩).operations (n + j * 12)) := by
    intro j hj
    have h := hwfold ⟨j, hj⟩
    simp only [jointLadderBody_localLength] at h
    rw [foldlAcc_eq_ladder tables rb sb acc0 n j hj] at h
    exact h
  have hstep : ∀ (j : Nat) (hj : j < 255),
      ladInv (goodOffsetAffinePt H hH) Qpt Rpt env.toEnvironment rb sb j
        (Fin.foldl j (fun acc (i : Fin j) =>
          (jointLadderBody tables rb sb acc ⟨i.val, by omega⟩).output (n + i.val * 12))
          acc0) →
      ladInv (goodOffsetAffinePt H hH) Qpt Rpt env.toEnvironment rb sb (j + 1)
        ((jointLadderBody tables rb sb
          (Fin.foldl j (fun acc (i : Fin j) =>
            (jointLadderBody tables rb sb acc ⟨i.val, by omega⟩).output (n + i.val * 12))
            acc0) ⟨j, hj⟩).output (n + j * 12)) := by
    intro j hj hacc
    have hwj := hwin j hj
    rw [jointLadderBody_ops, ulwc_append] at hwj
    simp only [mux4W_localLength] at hwj
    have hm := mux4W_soundness_of_ulwc _ _ _ _ _ _ env (n + j * 12) hwj.1
    have hDx := hj1_dx_of_ladInv env.toEnvironment eb rb sb Qpt Rpt H hH hgood tables n
      hb hb' htab j hj _ hm hacc
    have hrows := elm_rows123_of_ulwc _ _ env (n + j * 12 + 6) hwj.2 hDx
    have hDx2 := hj2_dx_of_ladInv env.toEnvironment eb rb sb Qpt Rpt H hH hgood tables n
      hb hb' htab j hj _ hm hDx hrows.1 hrows.2 hacc
    have hc := jointLadderBody_soundness_of_ulwc tables rb sb _ ⟨j, hj⟩ env (n + j * 12)
      hwj.1 hwj.2 hDx hDx2
    exact jointLadderBody_ladInv_step env.toEnvironment (goodOffsetAffinePt H hH) Qpt Rpt
      tables rb sb n j hj _ hb hb' htab hacc hc
  have hP := fin_foldl_inv' (fun acc (i : Fin 255) =>
      (jointLadderBody tables rb sb acc i).output (n + i.val * 12)) acc0
    (fun k acc => ladInv (goodOffsetAffinePt H hH) Qpt Rpt env.toEnvironment rb sb k acc)
    hacc0 hstep
  intro j
  rw [jlAcc_eq_foldl acc0 tables rb sb n j.val j.isLt]
  exact hP j.val (by omega)

end StandardECDSA
