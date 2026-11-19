/-
# Honest-witness denominators (task G1-c, ladder part)

`CompleteWitness` (`StandardECDSA/Main.lean`) carries the ladder denominators
`hj1`, `hj2`, `hjf1`, `hjf2` as explicit hypotheses.  This module discharges
`hj1` and `hj2` from `GoodOffset`.

Per returning step `j < 255`:

* `hj1 j` is `x(T_j) - x(C_j) ≠ 0`, where `T_j` is the `mux4W` output and `C_j`
  the fold accumulator;
* `hj2 j` is `x(C_j) - x(C_j + T_j) ≠ 0`, where `C_j + T_j` is the `elm` output.

With `σ_j = (-1)^j`, `C_j = (-1)^(j+1)·H + bitSum_j·Q + bitSumT_j·R` and
`T_j = 3σ_j·H + b0·Q + b1·R`, so the two bad equations of `hj1` are
`T_j = ±C_j` and those of `hj2` are `C_j = ±(C_j + T_j)`.  They are exactly the
`ladStep` slots (coefficients 4 and 2) and the `ladDbl` slots (coefficients 1
and 3) of `Math/OffsetFamily.lean`, read through the integer-coefficient bridge
`X_ne_of_avoids_zsmul` of `Phases/HonestShifted.lean`.

Every proof is complete; no new axioms and no `native_decide`.
-/

import StandardECDSA.Main
import StandardECDSA.Phases.HonestShifted

namespace StandardECDSA

open WeierstrassCurve StandardECDSA StandardECDSA.Gadgets StandardECDSA.Phases
  StandardECDSA.Math
open StandardECDSA.Math.FixedTables

/-! ## The prefix invariant of the 255-step fold -/

/-- The fold prefix `Fin.foldl j …` is the `jlAcc` of `Main.lean`. -/
theorem jlAcc_eq_foldl (acc0 : Pt) (tables : Tables) (rb sb : Vector E 256) (n : Nat)
    (j : Nat) (hj : j < 255) :
    jlAcc acc0 tables rb sb n ⟨j, hj⟩
      = Fin.foldl j (fun acc (i : Fin j) =>
          (jointLadderBody tables rb sb acc ⟨i.val, by omega⟩).output (n + i.val * 12)) acc0 := by
  rw [jlAcc_eq, foldlAcc_eq_ladder tables rb sb acc0 n j hj]

set_option linter.constructorNameAsVariable false in
/-- **The signed-offset prefix invariant of the joint ladder**, extracted from
the phase rows.  For every `j < 255` the fold accumulator represents
`ladAcc … j`. -/
theorem jointLadder_ladInv (env : Environment Fp) (Hpt Qpt Rpt : Affine.Point Wp)
    (acc0 : Pt) (tables : Tables) (rb sb : Vector E 256) (target : Pt) (n : Nat)
    (hacc0 : ∃ hns : NS (Expression.eval env acc0.1) (Expression.eval env acc0.2),
      Affine.Point.some (Expression.eval env acc0.1) (Expression.eval env acc0.2) hns = -Hpt)
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
    (hc : ConstraintsHold.Soundness env ((jointLadder acc0 tables rb sb target n).2)) :
    ∀ (j : Nat) (hj : j < 255),
      ladInv Hpt Qpt Rpt env rb sb j (jlAcc acc0 tables rb sb n ⟨j, hj⟩) := by
  have hL2 : (jointLadder acc0 tables rb sb target n).2
      = (jointLadder acc0 tables rb sb target).operations n := rfl
  rw [hL2, jointLadder_ops] at hc
  simp only [ConstraintsHold.Soundness] at hc
  rw [Operations.forAllNoOffset_append] at hc
  obtain ⟨hc1, _⟩ := hc
  rw [Circuit.foldlRange.forAllNoOffset] at hc1
  have hcl : ∀ i : Fin 255, (jointLadderBody tables rb sb default i).localLength = 12 := by
    intro i
    simp only [jointLadderBody, mux4W_localLength, elm_localLength, Circuit.localLength,
      Operations.append_localLength]
  have hinit : ladInv Hpt Qpt Rpt env rb sb 0 acc0 := hacc0
  have hstep : ∀ (j : Nat) (hj : j < 255),
      ladInv Hpt Qpt Rpt env rb sb j
        (Fin.foldl j (fun acc (i : Fin j) =>
          (jointLadderBody tables rb sb acc ⟨i.val, by omega⟩).output (n + i.val * 12)) acc0) →
      ladInv Hpt Qpt Rpt env rb sb (j + 1)
        ((jointLadderBody tables rb sb
          (Fin.foldl j (fun acc (i : Fin j) =>
            (jointLadderBody tables rb sb acc ⟨i.val, by omega⟩).output (n + i.val * 12)) acc0)
          ⟨j, hj⟩).output (n + j * 12)) := by
    intro j hj hacc
    obtain ⟨hns, hval⟩ := hacc
    have hcj := hc1 ⟨j, hj⟩
    rw [hcl ⟨j, hj⟩] at hcj
    rw [foldlAcc_eq_ladder tables rb sb acc0 n j hj] at hcj
    simp only [jointLadderBody_ops] at hcj
    rw [Operations.forAllNoOffset_append] at hcj
    obtain ⟨hm, he⟩ := hcj
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
  have hP := fin_foldl_inv' (fun acc (i : Fin 255) =>
      (jointLadderBody tables rb sb acc i).output (n + i.val * 12)) acc0
    (fun k acc => ladInv Hpt Qpt Rpt env rb sb k acc) hinit hstep
  intro j hj
  rw [jlAcc_eq_foldl acc0 tables rb sb n j hj]
  exact hP j (by omega)

/-! ## The four ladder slot targets, in affine form -/

/-- `sigmaZ` and `sigma` are the same function. -/
theorem sigmaZ_eq_sigma (j : Nat) : sigmaZ j = sigma j := rfl

/-- The `ladStep` slot `(j, false)`: `[4]H = σ_j·(B_j - b0·Q - b1·R)`. -/
theorem famOf_target_ladStep_false (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) (j : Fin 256) :
    (famOf env eb rb sb Qpt Rpt).toAffine.target
        (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (j, false)))))))
      = sigma j.val • (ladOff env Qpt Rpt rb sb j.val
          + -((rBitAt env rb j.val) • Qpt) + -((tBitAt env sb j.val) • Rpt)) := by
  show toAff ((famOf env eb rb sb Qpt Rpt).target
    (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (j, false)))))))) = _
  rw [famOf_target_apply]
  simp only [targetOf, toAff_toProjective, sigmaZ_eq_sigma]

/-- The `ladStep` slot `(j, true)`: `[2]H = σ_j·(-B_j - b0·Q - b1·R)`. -/
theorem famOf_target_ladStep_true (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) (j : Fin 256) :
    (famOf env eb rb sb Qpt Rpt).toAffine.target
        (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (j, true)))))))
      = sigma j.val • (-(ladOff env Qpt Rpt rb sb j.val)
          + -((rBitAt env rb j.val) • Qpt) + -((tBitAt env sb j.val) • Rpt)) := by
  show toAff ((famOf env eb rb sb Qpt Rpt).target
    (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (j, true)))))))) = _
  rw [famOf_target_apply]
  simp only [targetOf, toAff_toProjective, sigmaZ_eq_sigma]

/-- The `ladDbl` slot `(j, false)`: `[1]H = σ_j·(-2·B_j - b0·Q - b1·R)`. -/
theorem famOf_target_ladDbl_false (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) (j : Fin 256) :
    (famOf env eb rb sb Qpt Rpt).toAffine.target
        (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (j, false)))))))
      = sigma j.val • ((-2 : ℤ) • (ladOff env Qpt Rpt rb sb j.val)
          + -((rBitAt env rb j.val) • Qpt) + -((tBitAt env sb j.val) • Rpt)) := by
  show toAff ((famOf env eb rb sb Qpt Rpt).target
    (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (j, false)))))))) = _
  rw [famOf_target_apply]
  simp only [targetOf, toAff_toProjective, sigmaZ_eq_sigma]

/-- The `ladDbl` slot `(j, true)`: `[3]H = σ_j·(-b0·Q - b1·R)`. -/
theorem famOf_target_ladDbl_true (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) (j : Fin 256) :
    (famOf env eb rb sb Qpt Rpt).toAffine.target
        (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (j, true)))))))
      = sigma j.val • (-((rBitAt env rb j.val) • Qpt) + -((tBitAt env sb j.val) • Rpt)) := by
  show toAff ((famOf env eb rb sb Qpt Rpt).target
    (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (j, true)))))))) = _
  rw [famOf_target_apply]
  simp only [targetOf, toAff_toProjective, sigmaZ_eq_sigma]

/-! ## `hj1`: `x(T_j) ≠ x(C_j)` -/

/-- A natural multiple is the corresponding integer multiple. -/
theorem nsmul_eq_zsmul_int (n : Nat) (P : Affine.Point Wp) : (n : ℤ) • P = n • P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_zsmul, ih, succ_nsmul, one_zsmul, add_comm]

set_option linter.constructorNameAsVariable false in
/-- **The first ladder denominator does not vanish.**  For every returning step
`j < 255`, the `mux4W` output's `x` differs from the accumulator's `x`. -/
theorem hj1_dx (env : Environment Fp) (eb : Vector E 256) (rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) (H : AffinePoint K) (hH : H.IsOnCurve params)
    (hgood : GoodOffset H hH (famOf env eb rb sb Qpt Rpt))
    (acc0 : Pt) (tables : Tables) (target : Pt) (n : Nat)
    (hacc0 : ∃ hns : NS (Expression.eval env acc0.1) (Expression.eval env acc0.2),
      Affine.Point.some (Expression.eval env acc0.1) (Expression.eval env acc0.2) hns
        = -goodOffsetAffinePt H hH)
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
    (hc : ConstraintsHold.Soundness env ((jointLadder acc0 tables rb sb target n).2))
    (j : Nat) (hj : j < 255) :
    Expression.eval env
        ((mux4W (rb.get ⟨255 - j, by omega⟩) (sb.get ⟨255 - j, by omega⟩)
          (tables.x0 j) (tables.x1 j) (tables.x2 j) (tables.x3 j)).output (n + j * 12)).1
      - Expression.eval env (jlAcc acc0 tables rb sb n ⟨j, hj⟩).1 ≠ 0 := by
  classical
  have hL2 : (jointLadder acc0 tables rb sb target n).2
      = (jointLadder acc0 tables rb sb target).operations n := rfl
  have hc0 := hc
  rw [hL2, jointLadder_ops] at hc0
  simp only [ConstraintsHold.Soundness] at hc0
  rw [Operations.forAllNoOffset_append] at hc0
  obtain ⟨hc1, _⟩ := hc0
  rw [Circuit.foldlRange.forAllNoOffset] at hc1
  have hcl : ∀ i : Fin 255, (jointLadderBody tables rb sb default i).localLength = 12 := by
    intro i
    simp only [jointLadderBody, mux4W_localLength, elm_localLength, Circuit.localLength,
      Operations.append_localLength]
  have hcj := hc1 ⟨j, hj⟩
  rw [hcl ⟨j, hj⟩] at hcj
  rw [foldlAcc_eq_ladder tables rb sb acc0 n j hj] at hcj
  simp only [jointLadderBody_ops] at hcj
  rw [Operations.forAllNoOffset_append] at hcj
  obtain ⟨hm, _⟩ := hcj
  obtain ⟨hTm, hTval⟩ :=
    mux4W_Tpt env (goodOffsetAffinePt H hH) Qpt Rpt tables rb sb j (by omega) (n + j * 12)
      hb hb' htab hm
  obtain ⟨hns, hval⟩ :=
    jointLadder_ladInv env (goodOffsetAffinePt H hH) Qpt Rpt acc0 tables rb sb target n
      hacc0 hb hb' htab hc j hj
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

/-! ## The `x`-coordinate of `p + q` read off the `elmCore` rows -/

/-- The `x`-coordinate `xu` allocated by `elmCore` is the `x`-coordinate of
`p + q` in the group. -/
theorem elmXu_group (env : Environment Fp) (p q : Pt) (m : Nat)
    (hA : NS (Expression.eval env p.1) (Expression.eval env p.2))
    (hB : NS (Expression.eval env q.1) (Expression.eval env q.2))
    (h : ConstraintsHold.Soundness env ((elm p q).operations m)) :
    ∃ hU : NS (env.get (m + 2))
        (ElmAlgebra.elmMiddleY (Expression.eval env p.1) (Expression.eval env p.2)
          (env.get (m + 2)) (env.get (m + 1))),
      Affine.Point.some (env.get (m + 2))
          (ElmAlgebra.elmMiddleY (Expression.eval env p.1) (Expression.eval env p.2)
            (env.get (m + 2)) (env.get (m + 1))) hU
        = Affine.Point.some (Expression.eval env p.1) (Expression.eval env p.2) hA
          + Affine.Point.some (Expression.eval env q.1) (Expression.eval env q.2) hB := by
  simp only [elm, elmCore, nonzero, circuit_norm, pm] at h
  obtain ⟨r1, r2, r3, r4, -, -⟩ := h
  simp only [eval_cst, eval_sc] at r1 r2 r3 r4
  rw [show m + 1 + 1 + 1 = m + 3 from by omega] at r4
  rw [show m + 1 + 1 = m + 2 from by omega] at r3 r4
  have hDx : Expression.eval env q.1 - Expression.eval env p.1 ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at r1
    norm_num at r1
  have h1 : env.get (m + 1) * (Expression.eval env q.1 - Expression.eval env p.1)
      = Expression.eval env q.2 - Expression.eval env p.2 := by
    linear_combination r2
  have h2 : env.get (m + 1) * env.get (m + 1)
      = Expression.eval env p.1 + Expression.eval env q.1 + env.get (m + 2) := by
    linear_combination r3
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

/-! ## `hj2`: `x(C_j) ≠ x(C_j + T_j)` -/

set_option linter.constructorNameAsVariable false in
/-- **The second ladder denominator does not vanish.**  For every returning step
`j < 255`, the accumulator's `x` differs from the `xu` allocated by `elmCore`,
which is the `x`-coordinate of `C_j + T_j`. -/
theorem hj2_dx (env : Environment Fp) (eb : Vector E 256) (rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) (H : AffinePoint K) (hH : H.IsOnCurve params)
    (hgood : GoodOffset H hH (famOf env eb rb sb Qpt Rpt))
    (acc0 : Pt) (tables : Tables) (target : Pt) (n : Nat)
    (hacc0 : ∃ hns : NS (Expression.eval env acc0.1) (Expression.eval env acc0.2),
      Affine.Point.some (Expression.eval env acc0.1) (Expression.eval env acc0.2) hns
        = -goodOffsetAffinePt H hH)
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
    (hc : ConstraintsHold.Soundness env ((jointLadder acc0 tables rb sb target n).2))
    (j : Nat) (hj : j < 255) :
    Expression.eval env (jlAcc acc0 tables rb sb n ⟨j, hj⟩).1
      - env.get (n + j * 12 + 6 + 2) ≠ 0 := by
  classical
  have hL2 : (jointLadder acc0 tables rb sb target n).2
      = (jointLadder acc0 tables rb sb target).operations n := rfl
  have hc0 := hc
  rw [hL2, jointLadder_ops] at hc0
  simp only [ConstraintsHold.Soundness] at hc0
  rw [Operations.forAllNoOffset_append] at hc0
  obtain ⟨hc1, _⟩ := hc0
  rw [Circuit.foldlRange.forAllNoOffset] at hc1
  have hcl : ∀ i : Fin 255, (jointLadderBody tables rb sb default i).localLength = 12 := by
    intro i
    simp only [jointLadderBody, mux4W_localLength, elm_localLength, Circuit.localLength,
      Operations.append_localLength]
  have hcj := hc1 ⟨j, hj⟩
  rw [hcl ⟨j, hj⟩] at hcj
  rw [foldlAcc_eq_ladder tables rb sb acc0 n j hj] at hcj
  simp only [jointLadderBody_ops] at hcj
  rw [Operations.forAllNoOffset_append] at hcj
  obtain ⟨hm, he⟩ := hcj
  obtain ⟨hTm, hTval⟩ :=
    mux4W_Tpt env (goodOffsetAffinePt H hH) Qpt Rpt tables rb sb j (by omega) (n + j * 12)
      hb hb' htab hm
  obtain ⟨hns, hval⟩ :=
    jointLadder_ladInv env (goodOffsetAffinePt H hH) Qpt Rpt acc0 tables rb sb target n
      hacc0 hb hb' htab hc j hj
  have hC : ladAcc (goodOffsetAffinePt H hH) Qpt Rpt env rb sb j
      = ((-1 : ℤ) ^ (j + 1)) • (goodOffsetAffinePt H hH)
        + (bitSum env rb j) • Qpt + (bitSumT env sb j) • Rpt := by
    rw [ladAcc_split, ladAccH_eq, ladAccQ_eq, ladAccR_eq]
  rw [hC] at hval
  have he' : ConstraintsHold.Soundness env
      ((elm (jlAcc acc0 tables rb sb n ⟨j, hj⟩)
        ((mux4W (rb.get ⟨255 - j, by omega⟩) (sb.get ⟨255 - j, by omega⟩)
          (tables.x0 j) (tables.x1 j) (tables.x2 j) (tables.x3 j)).output (n + j * 12))).operations
        (n + j * 12 + 6)) := by
    rw [jlAcc_eq_foldl acc0 tables rb sb n j hj]
    exact he
  have hXU := elmXu_group env (jlAcc acc0 tables rb sb n ⟨j, hj⟩)
    ((mux4W (rb.get ⟨255 - j, by omega⟩) (sb.get ⟨255 - j, by omega⟩)
      (tables.x0 j) (tables.x1 j) (tables.x2 j) (tables.x3 j)).output (n + j * 12))
    (n + j * 12 + 6) hns hTm he'
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
  have hPpt : Affine.Point.some (Expression.eval env (jlAcc acc0 tables rb sb n ⟨j, hj⟩).1)
        (Expression.eval env (jlAcc acc0 tables rb sb n ⟨j, hj⟩).2) hns
      = (-sigma j) • goodOffsetAffinePt H hH + B1 := by
    rw [hval, hB1]
    abel
  have hQpt : Affine.Point.some (env.get (n + j * 12 + 6 + 2))
        (ElmAlgebra.elmMiddleY (Expression.eval env (jlAcc acc0 tables rb sb n ⟨j, hj⟩).1)
          (Expression.eval env (jlAcc acc0 tables rb sb n ⟨j, hj⟩).2)
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

end StandardECDSA
