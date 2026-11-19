/-
# The ladder fields of `CompleteWitness` (task G2-c)

`CompleteWitness`'s six ladder fields `hj1`, `hj2`, `hjf1`..`hjf4` are the
ladder's per-step and final-step denominators.  They are collected here in a
separate structure so that the (large) statement and its proof get their own
elaboration budget, and so that `CompleteWitness_of_ulwc` can consume them with
a purely syntactic match.

No new axioms, no `native_decide`, no `sorry`.
-/
import StandardECDSA.Witness.CompleteWitnessOfULWC

namespace StandardECDSA

open Circuit
open StandardECDSA.Gadgets
open StandardECDSA.Phases
open StandardECDSA.Math
open StandardECDSA.Witness
open StandardECDSA.Math.FixedTables
open WeierstrassCurve

set_option linter.constructorNameAsVariable false in
/-- **The ladder fields of `CompleteWitness` for the honest environment.** -/
theorem main_ladder_denominators (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (pkX pkY digestLo digestHi r s : K) (fam : BadFamily Grp) (hm : fam.m < 1294)
    (hhint : env.hint = seedHint (generateSeed pkX pkY digestLo digestHi r s fam hm))
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hIn : InputEmbedding inp env pkX pkY digestLo digestHi r s)
    (hstd : standardVerify pkX pkY digestLo digestHi r s)
    (hlo : digestLo.val < 2 ^ 128) (hhi : digestHi.val < 2 ^ 128)
    (H : AffinePoint K) (hH : H.IsOnCurve params)
    (hHX : H.X = Expression.eval env.toEnvironment (seedPhase inp n).1.hx)
    (hHY : H.Y = Expression.eval env.toEnvironment (seedPhase inp n).1.hy)
    (hQnsE : NS (Expression.eval env.toEnvironment inp.pkX)
      (Expression.eval env.toEnvironment inp.pkY))
    (hRnsE : NS (Expression.eval env.toEnvironment (shR inp n).1)
      (Expression.eval env.toEnvironment (shR inp n).2))
    (hgood : GoodOffset H hH (famOf env.toEnvironment (fbEb inp n) (fbRb inp n) (fbSb inp n)
      (Affine.Point.some (Expression.eval env.toEnvironment inp.pkX)
        (Expression.eval env.toEnvironment inp.pkY) hQnsE)
      (Affine.Point.some (Expression.eval env.toEnvironment (shR inp n).1)
        (Expression.eval env.toEnvironment (shR inp n).2) hRnsE))) :
    LadderWitness inp env n := by
  classical
  set g := generateSeed pkX pkY digestLo digestHi r s fam hm with hg
  have hsc : ScalarFacts g (digestOf digestLo digestHi) r.val (StandardECDSA.n - s.val) :=
    generateSeed_scalarFacts pkX pkY digestLo digestHi r s fam hm hstd.2.2.1 hstd.2.2.2.1 hlo hhi
  set Qpt : Affine.Point Wp := Affine.Point.some (Expression.eval env.toEnvironment inp.pkX)
    (Expression.eval env.toEnvironment inp.pkY) hQnsE with hQptdef
  set Rpt : Affine.Point Wp := Affine.Point.some (Expression.eval env.toEnvironment (shR inp n).1)
    (Expression.eval env.toEnvironment (shR inp n).2) hRnsE with hRptdef
  have hbE : ∀ k : Fin 256,
      Expression.eval env.toEnvironment ((fbEb inp n).get k) = 0 ∨
        Expression.eval env.toEnvironment ((fbEb inp n).get k) = 1 := by
    intro k
    rw [ebGet_of_main inp g env n hhint hw k]
    exact hsc.digestBits_bool k
  have hbR : ∀ k : Fin 256,
      Expression.eval env.toEnvironment ((fbRb inp n).get k) = 0 ∨
        Expression.eval env.toEnvironment ((fbRb inp n).get k) = 1 := by
    intro k
    rw [rbGet_of_main inp g env n hhint hw k]
    exact hsc.rBits_bool k
  have hbS : ∀ k : Fin 256,
      Expression.eval env.toEnvironment ((fbSb inp n).get k) = 0 ∨
        Expression.eval env.toEnvironment ((fbSb inp n).get k) = 1 := by
    intro k
    rw [sbGet_of_main inp g env n hhint hw k]
    exact hsc.tBits_bool k
  have hdx0 := hfb0_of_ulwc inp env n H hH Qpt Rpt hHX hgood
  have hfb := hfb_of_ulwc inp env n H hH Qpt Rpt hHX hHY hgood hw hbE hdx0
  have hdx : ∀ (k : Nat) (hk : k < 128),
      Expression.eval env.toEnvironment ((fbMux (fbEb inp n) fixedTables ⟨k, hk⟩).output
        (off6 inp n + 4 + k * 5)).1
        - Expression.eval env.toEnvironment (Circuit.FoldlM.foldlAcc (off6 inp n + 4)
            (Vector.finRange 128) (fixedBaseBody (fbEb inp n) fixedTables)
            ((affAdd (fbH inp n) (cst shiftX, cst (-shiftY))).output (off6 inp n)) ⟨k, hk⟩).1
        ≠ 0 := by
    intro k hk
    rw [← fbAcc_eq']
    exact hfb ⟨k, hk⟩
  have hHns : NS (Expression.eval env.toEnvironment (fbH inp n).1)
      (Expression.eval env.toEnvironment (fbH inp n).2) :=
    ns_congr hHX.symm hHY.symm (nsOfOnCurve H hH)
  have hcFb := fixedBase_soundness_of_ulwc (fbH inp n) (fbEb inp n) env (off6 inp n)
    (main_ulwc_fixedBase inp env n hw) hdx0 hfb
  obtain ⟨hnsEp, hEp⟩ := fixedBase_spec env (fbH inp n) (fbEb inp n) (off6 inp n)
    hHns hbE hdx0 hdx hcFb
  have hHpt : Affine.Point.some (Expression.eval env.toEnvironment (fbH inp n).1)
      (Expression.eval env.toEnvironment (fbH inp n).2) hHns = goodOffsetAffinePt H hH := by
    rw [goodOffsetAffinePt_eq_some H hH hgood]
    exact some_congr hHX.symm hHY.symm hHns (nsOfOnCurve H hH)
  have hd0v := hd0_of_ulwc inp g env n _ _ _ digestLo digestHi hhint hw hsc hIn.2.2.1 rfl hlo
  have hd1v := hd1_of_ulwc inp g env n _ _ _ digestLo digestHi hhint hw hsc hIn.2.2.2.1 rfl hlo hhi
  have hEd : digestNat env.toEnvironment (fbEb inp n) = digestOf digestLo digestHi := by
    show leNat (fun i : Fin 256 =>
      (Expression.eval env.toEnvironment ((bitsPhase (off3 inp n)).1.eb.get i)).val)
      = digestOf digestLo digestHi
    rw [leNat_eb_eq_digest env.toEnvironment inp (bitsPhase (off3 inp n)).1 hd0v hd1v hbE]
    show (Digest.mk (Expression.eval env.toEnvironment inp.digestLo)
      (Expression.eval env.toEnvironment inp.digestHi)).toNat = digestOf digestLo digestHi
    rw [hIn.2.2.1, hIn.2.2.2.1]
    rfl
  have hEpP : Affine.Point.some
        (Expression.eval env.toEnvironment ((fixedBase (fbH inp n) (fbEb inp n)).output (off6 inp n)).1)
        (Expression.eval env.toEnvironment ((fixedBase (fbH inp n) (fbEb inp n)).output (off6 inp n)).2)
        hnsEp
      = goodOffsetAffinePt H hH + digestOf digestLo digestHi •
          WeierstrassCurve.Projective.Point.toAffineLift Gpt := by
    rw [hEp, hHpt, hEd, toAffineLift_nsmul]
  have hnsEp' : NS (Expression.eval env.toEnvironment (jlTarget inp n).1)
      (Expression.eval env.toEnvironment (jlTarget inp n).2) :=
    ns_congr (hx := rfl) (hy := eval_neg env.toEnvironment _) (h := negPt_ns hnsEp)
  have hneg' : Affine.Point.some (Expression.eval env.toEnvironment (jlTarget inp n).1)
      (Expression.eval env.toEnvironment (jlTarget inp n).2) hnsEp'
      = -(goodOffsetAffinePt H hH + digestOf digestLo digestHi •
          WeierstrassCurve.Projective.Point.toAffineLift Gpt) := by
    calc Affine.Point.some (Expression.eval env.toEnvironment (jlTarget inp n).1)
          (Expression.eval env.toEnvironment (jlTarget inp n).2) hnsEp'
        = Affine.Point.some
            (Expression.eval env.toEnvironment ((fixedBase (fbH inp n) (fbEb inp n)).output (off6 inp n)).1)
            (-(Expression.eval env.toEnvironment ((fixedBase (fbH inp n) (fbEb inp n)).output (off6 inp n)).2))
            (negPt_ns hnsEp) :=
          some_congr (hx := rfl) (hy := eval_neg env.toEnvironment _) (h := hnsEp')
            (h' := negPt_ns hnsEp)
      _ = -Affine.Point.some
            (Expression.eval env.toEnvironment ((fixedBase (fbH inp n) (fbEb inp n)).output (off6 inp n)).1)
            (Expression.eval env.toEnvironment ((fixedBase (fbH inp n) (fbEb inp n)).output (off6 inp n)).2)
            hnsEp :=
          negPt_group _ _ hnsEp
      _ = -(goodOffsetAffinePt H hH + digestOf digestLo digestHi •
            WeierstrassCurve.Projective.Point.toAffineLift Gpt) := by rw [hEpP]
  have hacc0 := jlAcc0_neg inp env n H hH hHX hHY hQnsE hRnsE hgood
  have htab := shiftedTables_htab_of_main inp env n H hH Qpt Rpt hHX hHY hQnsE rfl hRnsE rfl
    hgood hw
  have hQns : NS ({ X := pkX, Y := pkY } : AffinePoint K).X
      ({ X := pkX, Y := pkY } : AffinePoint K).Y := nsOfOnCurve _ hstd.1
  have hQpt : Qpt = Affine.Point.some ({ X := pkX, Y := pkY } : AffinePoint K).X
      ({ X := pkX, Y := pkY } : AffinePoint K).Y hQns :=
    some_congr hIn.1 hIn.2.1 hQnsE hQns
  have hRns := hRns_of_generateSeed pkX pkY digestLo digestHi r s fam hm hstd
  have hRy : (affinePt (stdV { X := pkX, Y := pkY } r s (digestOf digestLo digestHi))).Y
      = Expression.eval env.toEnvironment (shR inp n).2 := by
    rw [eval_shR_y inp env n pkX pkY digestLo digestHi r s fam hm hhint hw,
      ← generateSeed_R_eq pkX pkY digestLo digestHi r s fam hm]
    rfl
  have hRpt : Rpt = Affine.Point.some
      (affinePt (stdV { X := pkX, Y := pkY } r s (digestOf digestLo digestHi))).X
      (affinePt (stdV { X := pkX, Y := pkY } r s (digestOf digestLo digestHi))).Y hRns :=
    some_congr (eval_shR_x inp env n pkX pkY digestLo digestHi r s fam hm hhint hw hIn hstd)
      hRy.symm hRnsE hRns
  obtain ⟨hj1v, hj2v, hjf1v, hjf2v, hjf3v, hjf4v⟩ :=
    jointLadder_denominators_of_ulwc env (fbEb inp n) (fbRb inp n)
    (fbSb inp n) Qpt Rpt H hH hgood (jlAcc0 inp n) (jlTables inp n) (jlTarget inp n) (off8 inp n)
    hacc0 hbR hbS htab (main_ulwc_jointLadder inp env n hw)
    (r := r) (s := s) (digestOf digestLo digestHi) { X := pkX, Y := pkY } hstd.1 hQns hRns
    hQpt hRpt (goodOffsetAffinePt H hH + digestOf digestLo digestHi •
      WeierstrassCurve.Projective.Point.toAffineLift Gpt)
    hnsEp' rfl hneg' hstd.2.2.2.1 hstd.2.2.2.2.1 hstd.2.2.2.2.2.1
    (leNat_rb_of_main inp g env n _ _ _ hhint hw hsc)
    (leNat_sb_of_main inp g env n _ _ _ hhint hw hsc)
  exact ⟨hj1v, hj2v, hjf1v, hjf2v, hjf3v, hjf4v⟩

end StandardECDSA
