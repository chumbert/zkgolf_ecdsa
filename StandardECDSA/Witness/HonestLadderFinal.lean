/-
# The final `elmTo` step of the ladder, from the group identity (gap G2)

`CompleteWitness`'s `hjf3`/`hjf4` are the two `elmTo` assert rows of the
ladder's final step.  They are *constraints*, not witness definitions, so they
cannot be read off `UsesLocalWitnessesCompleteness`; the honest prover knows
them because the group identity `2·C₂₅₅ + T₂₅₅ = target` holds.

This module supplies the two ingredients:

* `elmTo_rows_of_group` — the value-level algebra: the first four ELM rows plus
  the group identity `2·p + q = target` imply the two `elmTo` assert rows;
* `stdV_zero` — the standard verification equation
  `[E]G + [r]Q + [n-s]·R = O` for the textbook verification point `R = affinePt V`.

Gap G2 of `docs/m6-report.md`.
-/
import StandardECDSA.Phases.HonestLadderPhase
import StandardECDSA.Math.SignatureEquation

namespace StandardECDSA

open WeierstrassCurve StandardECDSA.Gadgets StandardECDSA.Math StandardECDSA.Phases

/-! ## The `elmTo` assert rows from the group identity -/

/-- **The two `elmTo` assert rows follow from the group identity.**  Given the
first four ELM rows (which `UsesLocalWitnessesCompleteness` pins) and
`2·p + q = target`, the two remaining rows hold. -/
theorem elmTo_rows_of_group (env : Environment Fp) (p q target : Pt) (m : Nat)
    (hA : NS (Expression.eval env p.1) (Expression.eval env p.2))
    (hB : NS (Expression.eval env q.1) (Expression.eval env q.2))
    (hT : NS (Expression.eval env target.1) (Expression.eval env target.2))
    (hgrp : 2 • Affine.Point.some (Expression.eval env p.1) (Expression.eval env p.2) hA
        + Affine.Point.some (Expression.eval env q.1) (Expression.eval env q.2) hB
      = Affine.Point.some (Expression.eval env target.1) (Expression.eval env target.2) hT)
    (e1 : (Expression.eval env q.1 - Expression.eval env p.1) * env.get m = 1)
    (e2 : (Expression.eval env q.1 - Expression.eval env p.1) * env.get (m + 1)
      = Expression.eval env q.2 - Expression.eval env p.2)
    (e3 : env.get (m + 1) * env.get (m + 1) - Expression.eval env p.1
      - Expression.eval env q.1 - env.get (m + 2) = 0)
    (e4 : (env.get (m + 1) + env.get (m + 3)) * (Expression.eval env p.1 - env.get (m + 2))
      - 2 * Expression.eval env p.2 = 0) :
    (env.get (m + 3) * env.get (m + 3) - Expression.eval env p.1 - env.get (m + 2)
        - Expression.eval env target.1 = 0) ∧
    (env.get (m + 3) * (Expression.eval env p.1 - Expression.eval env target.1)
        - Expression.eval env p.2 - Expression.eval env target.2 = 0) := by
  classical
  set x := env.get (m + 3) * env.get (m + 3) - Expression.eval env p.1 - env.get (m + 2)
    with hx
  set y := env.get (m + 3) * (Expression.eval env p.1 - x) - Expression.eval env p.2
    with hy
  have hEqs : elmEqs #v[Expression.eval env p.1, Expression.eval env p.2,
      Expression.eval env q.1, Expression.eval env q.2] (x, y) :=
    ⟨env.get m, env.get (m + 1), env.get (m + 2), env.get (m + 3), e1, e2, e3, e4,
      by rw [hx]; simp, by rw [hy]; simp⟩
  obtain ⟨hR, hval⟩ := elmEqs_group _ _ hA hB hEqs
  have hxy := hval.trans hgrp
  simp only [Affine.Point.some.injEq] at hxy
  obtain ⟨h1, h2⟩ := hxy
  refine ⟨?_, ?_⟩
  · exact sub_eq_zero.mpr h1
  · rw [← h1, ← hy, ← h2, sub_self]

/-! ## The standard verification equation -/

/-- **The standard verification equation.**  For a standard-valid signature the
textbook verification point `V = [u₁]G + [u₂]Q` satisfies
`[E]G + [r]Q + [n-s]·R = O` with `R = affinePt V`. -/
theorem stdV_zero (Q : AffinePoint K) (hQ : Q.IsOnCurve params)
    {r s : K} (hs0 : 0 < s.val) (hsn : s.val < n) (E : Nat)
    (hVne : ¬ ProjectiveEquiv (stdV Q r s E) infinityPoint) :
    E • Gpt + r.val • Qpt Q hQ
      + (n - s.val) • (affinePt (stdV Q r s E)).toProjective.toMathlibPoint params
          (toProjective_on_curve (affinePt_isOnCurve (stdV_on_curve Q hQ r s E)
            (fun hz => hVne ((Z_eq_zero_iff_equiv_infinity
              (stdV_on_curve Q hQ r s E)).mp hz)))) = 0 := by
  have hsw : s.val * invModN s.val % n = 1 := s_mul_invModN s.val hs0 hsn
  have hV_on : (stdV Q r s E).IsOnCurve params := stdV_on_curve Q hQ r s E
  have hVz : (stdV Q r s E).Z ≠ 0 := fun hz =>
    hVne ((Z_eq_zero_iff_equiv_infinity hV_on).mp hz)
  have hR_on : (affinePt (stdV Q r s E)).IsOnCurve params := affinePt_isOnCurve hV_on hVz
  have hRp_on : (affinePt (stdV Q r s E)).toProjective.IsOnCurve params :=
    toProjective_on_curve hR_on
  have hVpt : (stdV Q r s E).toMathlibPoint params hV_on
      = (E * invModN s.val % n) • Gpt + (r.val * invModN s.val % n) • Qpt Q hQ :=
    stdV_toMathlib Q hQ r s E hV_on
  have hVeq : ProjectiveEquiv (stdV Q r s E) (affinePt (stdV Q r s E)).toProjective :=
    projectiveEquiv_affinePt hVz
  have hVeq_pt : (stdV Q r s E).toMathlibPoint params hV_on
      = (affinePt (stdV Q r s E)).toProjective.toMathlibPoint params hRp_on :=
    (projectiveEquiv_iff_toMathlib (stdV Q r s E) (affinePt (stdV Q r s E)).toProjective
      hV_on hRp_on).mp hVeq
  have hRpt_eq : (affinePt (stdV Q r s E)).toProjective.toMathlibPoint params hRp_on
      = (E * invModN s.val % n) • Gpt + (r.val * invModN s.val % n) • Qpt Q hQ := by
    rw [← hVpt]
    exact hVeq_pt.symm
  exact (signature_equation_iff (E := E) (r := r.val) (s := s.val) (w := invModN s.val)
    (u1 := E * invModN s.val % n) (u2 := r.val * invModN s.val % n) (t := n - s.val)
    hs0 hsn hsw rfl rfl rfl Gpt (Qpt Q hQ) _).mpr hRpt_eq

/-! ## The affine form of the standard verification equation -/

/-- **The standard verification equation, in the affine group.** -/
theorem stdV_zero_affine (Q : AffinePoint K) (hQ : Q.IsOnCurve params) (hQns : NS Q.X Q.Y)
    {r s : K} (hs0 : 0 < s.val) (hsn : s.val < n) (E : Nat)
    (hVne : ¬ ProjectiveEquiv (stdV Q r s E) infinityPoint)
    (hRns : NS (affinePt (stdV Q r s E)).X (affinePt (stdV Q r s E)).Y) :
    E • Projective.Point.toAffineLift Gpt + r.val • Affine.Point.some Q.X Q.Y hQns
      + (n - s.val) • Affine.Point.some (affinePt (stdV Q r s E)).X
          (affinePt (stdV Q r s E)).Y hRns = 0 := by
  have h := congrArg (fun P => Projective.Point.toAffineLift P)
    (stdV_zero Q hQ hs0 hsn E hVne)
  have hgoal : Projective.Point.toAffineLift (E • Gpt + r.val • Qpt Q hQ
      + (n - s.val) • (affinePt (stdV Q r s E)).toProjective.toMathlibPoint params
          (toProjective_on_curve (affinePt_isOnCurve (stdV_on_curve Q hQ r s E)
            (fun hz => hVne ((Z_eq_zero_iff_equiv_infinity
              (stdV_on_curve Q hQ r s E)).mp hz)))))
      = E • Projective.Point.toAffineLift Gpt + r.val • Affine.Point.some Q.X Q.Y hQns
        + (n - s.val) • Affine.Point.some (affinePt (stdV Q r s E)).X
            (affinePt (stdV Q r s E)).Y hRns := by
    rw [toAffineLift_add, toAffineLift_add, toAffineLift_nsmul, toAffineLift_nsmul,
      toAffineLift_nsmul, toAffineLift_Qpt Q hQ hQns,
      toAffineLift_toMathlibPoint (affinePt (stdV Q r s E))
        (affinePt_isOnCurve (stdV_on_curve Q hQ r s E)
          (fun hz => hVne ((Z_eq_zero_iff_equiv_infinity
            (stdV_on_curve Q hQ r s E)).mp hz))) hRns]
  exact hgoal.symm.trans (h.trans toAffineLift_zero)

/-- **The target identity.**  From the standard verification equation and
`target = -ep`, `ep = H + [E]G`, the ladder's target is `[r]Q + [t]R - H`. -/
theorem target_eq_of_zero (Hpt QptA RptA ep target : Affine.Point Wp) (E r t : Nat)
    (hep : ep = Hpt + E • Projective.Point.toAffineLift Gpt)
    (hneg : target = -ep)
    (hzero : E • Projective.Point.toAffineLift Gpt + r • QptA + t • RptA = 0) :
    target = (r : ℤ) • QptA + (t : ℤ) • RptA - Hpt := by
  have h0 : (r • QptA + t • RptA) + E • Projective.Point.toAffineLift Gpt = 0 := by
    rw [← hzero]; abel
  have h : E • Projective.Point.toAffineLift Gpt = -(r • QptA + t • RptA) :=
    eq_neg_of_add_eq_zero_right h0
  rw [hneg, hep, h,
    show (r : ℤ) • QptA = r • QptA from
      Nat.cast_smul_eq_nsmul (M := Affine.Point Wp) (R := ℤ) r _,
    show (t : ℤ) • RptA = t • RptA from
      Nat.cast_smul_eq_nsmul (M := Affine.Point Wp) (R := ℤ) t _]
  abel

set_option linter.constructorNameAsVariable false in
/-- **The ladder's final group identity.**  After 256 steps the ladder represents
`[r]Q + [t]R - H`, which is exactly the final `elmTo`'s target. -/
theorem ladAcc_256_eq_target (env : ProverEnvironment Fp) {r s : K} (Ed : Nat)
    (H : AffinePoint K) (hH : H.IsOnCurve params) (Qpt Rpt : Affine.Point Wp)
    (rb sb : Vector E 256) (Q : AffinePoint K) (hQ : Q.IsOnCurve params)
    (hQns : NS Q.X Q.Y)
    (hRns : NS (affinePt (stdV Q r s Ed)).X (affinePt (stdV Q r s Ed)).Y)
    (hQpt : Qpt = Affine.Point.some Q.X Q.Y hQns)
    (hRpt : Rpt = Affine.Point.some (affinePt (stdV Q r s Ed)).X
      (affinePt (stdV Q r s Ed)).Y hRns)
    (target : Pt) (ep : Affine.Point Wp)
    (hTgt : NS (Expression.eval env.toEnvironment target.1)
      (Expression.eval env.toEnvironment target.2))
    (hep : ep = goodOffsetAffinePt H hH + Ed • Projective.Point.toAffineLift Gpt)
    (hneg : Affine.Point.some (Expression.eval env.toEnvironment target.1)
        (Expression.eval env.toEnvironment target.2) hTgt = -ep)
    (hs0 : 0 < s.val) (hsn : s.val < n)
    (hVne : ¬ ProjectiveEquiv (stdV Q r s Ed) infinityPoint)
    (hb : ∀ k : Fin 256, Expression.eval env.toEnvironment (rb.get k) = 0 ∨
      Expression.eval env.toEnvironment (rb.get k) = 1)
    (hb' : ∀ k : Fin 256, Expression.eval env.toEnvironment (sb.get k) = 0 ∨
      Expression.eval env.toEnvironment (sb.get k) = 1)
    (hr : (leNat (fun k : Fin 256 =>
      (Expression.eval env.toEnvironment (rb.get k)).val) : ℤ) = r.val)
    (ht : (leNat (fun k : Fin 256 =>
      (Expression.eval env.toEnvironment (sb.get k)).val) : ℤ) = ((n - s.val : Nat) : ℤ)) :
    ladAcc (goodOffsetAffinePt H hH) Qpt Rpt env.toEnvironment rb sb 256
      = Affine.Point.some (Expression.eval env.toEnvironment target.1)
          (Expression.eval env.toEnvironment target.2) hTgt := by
  rw [ladAcc_256 (goodOffsetAffinePt H hH) Qpt Rpt env.toEnvironment rb sb hb hb', hr, ht]
  subst hQpt
  subst hRpt
  have hzero : Ed • Projective.Point.toAffineLift Gpt
      + r.val • Affine.Point.some Q.X Q.Y hQns
      + (n - s.val) • Affine.Point.some (affinePt (stdV Q r s Ed)).X
          (affinePt (stdV Q r s Ed)).Y hRns = 0 :=
    stdV_zero_affine Q hQ hQns hs0 hsn Ed hVne hRns
  have htarget := target_eq_of_zero (goodOffsetAffinePt H hH)
    (Affine.Point.some Q.X Q.Y hQns)
    (Affine.Point.some (affinePt (stdV Q r s Ed)).X (affinePt (stdV Q r s Ed)).Y hRns)
    ep (Affine.Point.some (Expression.eval env.toEnvironment target.1)
      (Expression.eval env.toEnvironment target.2) hTgt) Ed r.val (n - s.val)
    hep hneg hzero
  exact htarget.symm

end StandardECDSA
