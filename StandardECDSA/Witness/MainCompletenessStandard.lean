/-
# Completeness for every standard-valid input (task G2-c, final theorem)

`Witness/MainCompleteness.lean` proves `CompleteWitness` for the honest
environment, but takes the offset `H` and the fact `GoodOffset H hH (famOf env …)`
as hypotheses.  The obstacle is the *offset fixed point*: `generateSeed` picks
`H = Seed.H (generateSeed … fam hm)`, i.e. the offset point of the family `fam`
it is given, while `CompleteWitness` needs the family `famOf env …` of the
environment that `generateSeed` produces.

The fixed point is broken by `Witness/FamilyInvariance.lean`: `famOf` depends on
the environment only through the bit wires `eb`, `rb`, `sb`, which are
`bitsOf E`, `bitsOf r.val` and `bitsOf (n - s.val)` — determined by the *input*,
not by the offset.  So the prover may pick the offset from a *reference*
environment `env0` (built from a vacuous family) and the resulting family is the
same one the real environment sees.

No new axioms, no `native_decide`, no `sorry`.
-/
import StandardECDSA.Witness.MainCompleteness
import StandardECDSA.Witness.Correctness
import StandardECDSA.WitgenCausality
import StandardECDSA.Cost
import StandardECDSA.NoLookupSub

namespace StandardECDSA

open Circuit
open StandardECDSA.Gadgets
open StandardECDSA.Phases
open StandardECDSA.Math
open StandardECDSA.Witness
open StandardECDSA.Math.FixedTables
open WeierstrassCurve

/-! ## Reading the input wires of a prover environment -/

/-- Wire `i` of a `fromList` environment is the `i`-th witness. -/
theorem eval_var_fromList (hint : ProverHint Fp) (w : List Fp) (i : Nat) :
    Expression.eval (ProverEnvironment.fromList w hint).toEnvironment
      (Expression.var (F := Fp) ⟨i⟩) = w[i]?.getD 0 := by
  rw [eval_var]
  rfl

/-- Wire `i` of `(main inp).proverEnvironment hint init` is `init[i]` for
`i < init.length`. -/
theorem eval_var_proverEnvironment (inp : Var Input Fp) (hint : ProverHint Fp)
    (init : List Fp) (i : Nat) (hi : i < init.length) :
    Expression.eval ((main inp).proverEnvironment hint init).toEnvironment
      (Expression.var (F := Fp) ⟨i⟩) = init.getD i 0 := by
  simp only [Circuit.proverEnvironment, eval_var_fromList,
    FlatOperation.getElem?_dynamicWitnesses_of_lt hi]
  simp [List.getElem?_eq_getElem hi]

/-- The input embedding of the concrete prover environment of `inputVar`. -/
theorem inputEmbedding_inputVar (hint : ProverHint Fp) (init : List Fp)
    (h0 : 0 < init.length) (h1 : 1 < init.length) (h2 : 2 < init.length)
    (h3 : 3 < init.length) (h4 : 4 < init.length) (h5 : 5 < init.length) :
    InputEmbedding inputVar ((main inputVar).proverEnvironment hint init)
      (init.getD 0 0) (init.getD 1 0) (init.getD 2 0) (init.getD 3 0)
      (init.getD 4 0) (init.getD 5 0) :=
  ⟨eval_var_proverEnvironment inputVar hint init 0 h0,
   eval_var_proverEnvironment inputVar hint init 1 h1,
   eval_var_proverEnvironment inputVar hint init 2 h2,
   eval_var_proverEnvironment inputVar hint init 3 h3,
   eval_var_proverEnvironment inputVar hint init 4 h4,
   eval_var_proverEnvironment inputVar hint init 5 h5⟩

/-- The public key of an embedded environment is nonsingular. -/
theorem main_QnsE (inp : Var Input Fp) (env : ProverEnvironment Fp)
    (pkX pkY digestLo digestHi r s : K)
    (hIn : InputEmbedding inp env pkX pkY digestLo digestHi r s)
    (hstd : standardVerify pkX pkY digestLo digestHi r s) :
    NS (Expression.eval env.toEnvironment inp.pkX)
      (Expression.eval env.toEnvironment inp.pkY) := by
  rw [hIn.1, hIn.2.1]
  exact nsOfOnCurve _ hstd.1

/-- The signature point of an embedded environment is nonsingular. -/
theorem main_RnsE (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (pkX pkY digestLo digestHi r s : K) (fam : BadFamily Grp) (hm : fam.m < 1294)
    (hhint : env.hint = seedHint (generateSeed pkX pkY digestLo digestHi r s fam hm))
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hIn : InputEmbedding inp env pkX pkY digestLo digestHi r s)
    (hstd : standardVerify pkX pkY digestLo digestHi r s) :
    NS (Expression.eval env.toEnvironment (shR inp n).1)
      (Expression.eval env.toEnvironment (shR inp n).2) :=
  ns_congr
    (eval_shR_x inp env n pkX pkY digestLo digestHi r s fam hm hhint hw hIn hstd)
    (eval_shR_y inp env n pkX pkY digestLo digestHi r s fam hm hhint hw)
    (hRns_of_generateSeed pkX pkY digestLo digestHi r s fam hm hstd)

/-! ## The vacuous reference family -/

/-- The vacuous bad-equation family (`m = 0`). -/
def vacuousFamily : BadFamily Grp where
  m := 0
  coeff := fun i => i.elim0
  coeff_pos := fun i => i.elim0
  coeff_lt := fun i => i.elim0
  target := fun i => i.elim0

theorem vacuousFamily_m : vacuousFamily.m < 1294 := by decide

/-! ## The offset fixed point -/

/-- **The family of the honest environment is the reference family.**  Two
environments with the same bit wires see the same `famOf`, and `famOf` is
insensitive to the choice of the two points up to equality. -/
theorem main_famOf_eq (inp : Var Input Fp) (n : Nat)
    (env0 env : ProverEnvironment Fp) (g0 g : Witness.Seed)
    (hhint0 : env0.hint = seedHint g0) (hhint : env.hint = seedHint g)
    (hw0 : env0.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hdb : g.digestBits = g0.digestBits) (hrb' : g.rBits = g0.rBits)
    (hsb' : g.tBits = g0.tBits)
    (Qpt0 Rpt0 Qpt Rpt : Affine.Point Wp) (hQ : Qpt = Qpt0) (hR : Rpt = Rpt0) :
    famOf env.toEnvironment (fbEb inp n) (fbRb inp n) (fbSb inp n) Qpt Rpt
      = famOf env0.toEnvironment (fbEb inp n) (fbRb inp n) (fbSb inp n) Qpt0 Rpt0 := by
  rw [famOf_congr_pts env.toEnvironment _ _ _ hQ hR]
  exact famOf_congr env.toEnvironment env0.toEnvironment (fbEb inp n) (fbRb inp n)
    (fbSb inp n) Qpt0 Rpt0
    (fun k => by
      rw [ebGet_of_main inp g env n hhint hw k, ebGet_of_main inp g0 env0 n hhint0 hw0 k, hdb])
    (fun k => by
      rw [rbGet_of_main inp g env n hhint hw k, rbGet_of_main inp g0 env0 n hhint0 hw0 k, hrb'])
    (fun k => by
      rw [sbGet_of_main inp g env n hhint hw k, sbGet_of_main inp g0 env0 n hhint0 hw0 k, hsb'])

/-! ## The final theorem -/

/-- The data `CompleteWitness_of_ulwc` needs, bundled so that the construction
and the final application get separate elaboration budgets. -/
structure HonestWitnessData (pkX pkY digestLo digestHi r s : K) where
  env : ProverEnvironment Fp
  fam : BadFamily Grp
  hm : fam.m < 1294
  hhint : env.hint = seedHint (generateSeed pkX pkY digestLo digestHi r s fam hm)
  hw : env.UsesLocalWitnessesCompleteness 6 ((main inputVar).operations 6)
  hIn : InputEmbedding inputVar env pkX pkY digestLo digestHi r s
  H : AffinePoint K
  hH : H.IsOnCurve params
  hHX : H.X = Expression.eval env.toEnvironment (seedPhase inputVar 6).1.hx
  hHY : H.Y = Expression.eval env.toEnvironment (seedPhase inputVar 6).1.hy
  hQnsE : NS (Expression.eval env.toEnvironment inputVar.pkX)
    (Expression.eval env.toEnvironment inputVar.pkY)
  hRnsE : NS (Expression.eval env.toEnvironment (shR inputVar 6).1)
    (Expression.eval env.toEnvironment (shR inputVar 6).2)
  hgood : GoodOffset H hH (famOf env.toEnvironment (fbEb inputVar 6) (fbRb inputVar 6)
    (fbSb inputVar 6)
    (Affine.Point.some (Expression.eval env.toEnvironment inputVar.pkX)
      (Expression.eval env.toEnvironment inputVar.pkY) hQnsE)
    (Affine.Point.some (Expression.eval env.toEnvironment (shR inputVar 6).1)
      (Expression.eval env.toEnvironment (shR inputVar 6).2) hRnsE))

/-- The reference environment and its family, bundled so that the two halves of
the construction get separate elaboration budgets. -/
structure ReferenceData (pkX pkY digestLo digestHi r s : K) where
  env0 : ProverEnvironment Fp
  g0 : Witness.Seed
  hg0 : g0 = generateSeed pkX pkY digestLo digestHi r s vacuousFamily vacuousFamily_m
  hhint0 : env0.hint = seedHint g0
  hhint0' : env0.hint
    = seedHint (generateSeed pkX pkY digestLo digestHi r s vacuousFamily vacuousFamily_m)
  hw0 : env0.UsesLocalWitnessesCompleteness 6 ((main inputVar).operations 6)
  hIn0 : InputEmbedding inputVar env0 pkX pkY digestLo digestHi r s
  hQnsE0 : NS (Expression.eval env0.toEnvironment inputVar.pkX)
    (Expression.eval env0.toEnvironment inputVar.pkY)
  hRnsE0 : NS (Expression.eval env0.toEnvironment (shR inputVar 6).1)
    (Expression.eval env0.toEnvironment (shR inputVar 6).2)
  Qpt0 : Affine.Point Wp
  hQpt0 : Qpt0 = Affine.Point.some (Expression.eval env0.toEnvironment inputVar.pkX)
    (Expression.eval env0.toEnvironment inputVar.pkY) hQnsE0
  Rpt0 : Affine.Point Wp
  hRpt0 : Rpt0 = Affine.Point.some (Expression.eval env0.toEnvironment (shR inputVar 6).1)
    (Expression.eval env0.toEnvironment (shR inputVar 6).2) hRnsE0
  fam : BadFamily Grp
  hm : fam.m < 1294
  hfamdef : fam = famOf env0.toEnvironment (fbEb inputVar 6) (fbRb inputVar 6)
    (fbSb inputVar 6) Qpt0 Rpt0

set_option linter.constructorNameAsVariable false in
/-- **The reference environment of a standard-valid input.** -/
noncomputable def main_referenceData (pkX pkY digestLo digestHi r s : K)
    (hstd : standardVerify pkX pkY digestLo digestHi r s)
    (hlo : digestLo.val < 2 ^ 128) (hhi : digestHi.val < 2 ^ 128) :
    ReferenceData pkX pkY digestLo digestHi r s := by
  classical
  have hb0 : Below 6 inputVar.pkX := by simp [Below, inputVar]
  have hb1 : Below 6 inputVar.pkY := by simp [Below, inputVar]
  have hb2 : Below 6 inputVar.digestLo := by simp [Below, inputVar]
  have hb3 : Below 6 inputVar.digestHi := by simp [Below, inputVar]
  have hb4 : Below 6 inputVar.r := by simp [Below, inputVar]
  have hb5 : Below 6 inputVar.s := by simp [Below, inputVar]
  have hsc : ((main inputVar).operations 6).SubcircuitsConsistent 6 :=
    subcircuitsConsistent_of_subcircuits_nil (main_subcircuits_nil inputVar 6)
  set g0 := generateSeed pkX pkY digestLo digestHi r s vacuousFamily vacuousFamily_m with hg0
  set env0 := (main inputVar).proverEnvironment (seedHint g0) [pkX, pkY, digestLo, digestHi, r, s] with henv0
  have hhint0 : env0.hint = seedHint (generateSeed pkX pkY digestLo digestHi r s
      vacuousFamily vacuousFamily_m) := by rw [henv0, hg0]; rfl
  have hhint0s : env0.hint = seedHint g0 := by rw [henv0, hg0]; rfl
  have hw0 : env0.UsesLocalWitnessesCompleteness 6
      ((main inputVar).operations 6) :=
    ProverEnvironment.can_replace_usesLocalWitnessesCompleteness hsc
      (main_ulwc_exists inputVar (seedHint g0) [pkX, pkY, digestLo, digestHi, r, s] hb0 hb1 hb2 hb3 hb4 hb5)
  have hIn0 : InputEmbedding inputVar env0 pkX pkY digestLo digestHi r s :=
    inputEmbedding_inputVar (seedHint g0) [pkX, pkY, digestLo, digestHi, r, s] (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have hQnsE0 : NS (Expression.eval env0.toEnvironment inputVar.pkX)
      (Expression.eval env0.toEnvironment inputVar.pkY) :=
    main_QnsE inputVar env0 pkX pkY digestLo digestHi r s hIn0 hstd
  have hRnsE0 : NS (Expression.eval env0.toEnvironment (shR inputVar 6).1)
      (Expression.eval env0.toEnvironment (shR inputVar 6).2) :=
    main_RnsE inputVar env0 6 pkX pkY digestLo digestHi r s vacuousFamily
      vacuousFamily_m hhint0 hw0 hIn0 hstd
  let Qpt0 : Affine.Point Wp := Affine.Point.some
    (Expression.eval env0.toEnvironment inputVar.pkX)
    (Expression.eval env0.toEnvironment inputVar.pkY) hQnsE0
  let Rpt0 : Affine.Point Wp := Affine.Point.some
    (Expression.eval env0.toEnvironment (shR inputVar 6).1)
    (Expression.eval env0.toEnvironment (shR inputVar 6).2) hRnsE0
  let fam : BadFamily Grp := famOf env0.toEnvironment (fbEb inputVar 6)
    (fbRb inputVar 6) (fbSb inputVar 6) Qpt0 Rpt0
  have hm : fam.m < 1294 := famOf_m_lt_candidates _ _ _ _ _ _
  exact ⟨env0, g0, hg0, hhint0s, hhint0, hw0, hIn0, hQnsE0, hRnsE0, Qpt0, rfl, Rpt0, rfl,
    fam, hm, rfl⟩

set_option linter.constructorNameAsVariable false in
/-- **The honest witness data of a standard-valid input.** -/
noncomputable def main_honestData (pkX pkY digestLo digestHi r s : K)
    (hstd : standardVerify pkX pkY digestLo digestHi r s)
    (hlo : digestLo.val < 2 ^ 128) (hhi : digestHi.val < 2 ^ 128) :
    HonestWitnessData pkX pkY digestLo digestHi r s := by
  classical
  obtain ⟨env0, g0, hg0, hhint0, hhint0', hw0, hIn0, hQnsE0, hRnsE0, Qpt0, hQpt0,
    Rpt0, hRpt0, fam, hm, hfamdef⟩ := main_referenceData pkX pkY digestLo digestHi r s hstd hlo hhi
  have hb0 : Below 6 inputVar.pkX := by simp [Below, inputVar]
  have hb1 : Below 6 inputVar.pkY := by simp [Below, inputVar]
  have hb2 : Below 6 inputVar.digestLo := by simp [Below, inputVar]
  have hb3 : Below 6 inputVar.digestHi := by simp [Below, inputVar]
  have hb4 : Below 6 inputVar.r := by simp [Below, inputVar]
  have hb5 : Below 6 inputVar.s := by simp [Below, inputVar]
  have hsc : ((main inputVar).operations 6).SubcircuitsConsistent 6 :=
    subcircuitsConsistent_of_subcircuits_nil (main_subcircuits_nil inputVar 6)
  set g := generateSeed pkX pkY digestLo digestHi r s fam hm with hg
  set env := (main inputVar).proverEnvironment (seedHint g) [pkX, pkY, digestLo, digestHi, r, s] with henv
  have hhint : env.hint = seedHint (generateSeed pkX pkY digestLo digestHi r s fam hm) := by
    rw [henv, hg]; rfl
  have hw : env.UsesLocalWitnessesCompleteness 6
      ((main inputVar).operations 6) :=
    ProverEnvironment.can_replace_usesLocalWitnessesCompleteness hsc
      (main_ulwc_exists inputVar (seedHint g) [pkX, pkY, digestLo, digestHi, r, s] hb0 hb1 hb2 hb3 hb4 hb5)
  have hIn : InputEmbedding inputVar env pkX pkY digestLo digestHi r s :=
    inputEmbedding_inputVar (seedHint g) [pkX, pkY, digestLo, digestHi, r, s] (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have hQnsE : NS (Expression.eval env.toEnvironment inputVar.pkX)
      (Expression.eval env.toEnvironment inputVar.pkY) :=
    main_QnsE inputVar env pkX pkY digestLo digestHi r s hIn hstd
  have hRnsE : NS (Expression.eval env.toEnvironment (shR inputVar 6).1)
      (Expression.eval env.toEnvironment (shR inputVar 6).2) :=
    main_RnsE inputVar env 6 pkX pkY digestLo digestHi r s fam hm hhint hw hIn hstd
  have hQpt : Affine.Point.some (Expression.eval env.toEnvironment inputVar.pkX)
        (Expression.eval env.toEnvironment inputVar.pkY) hQnsE = Qpt0 := by
    rw [hQpt0]
    exact some_congr (hIn.1.trans hIn0.1.symm) (hIn.2.1.trans hIn0.2.1.symm) hQnsE hQnsE0
  have hxR : Expression.eval env.toEnvironment (shR inputVar 6).1
      = Expression.eval env0.toEnvironment (shR inputVar 6).1 :=
    (eval_shR_x inputVar env 6 pkX pkY digestLo digestHi r s fam hm hhint hw hIn hstd).trans
      (eval_shR_x inputVar env0 6 pkX pkY digestLo digestHi r s vacuousFamily
        vacuousFamily_m hhint0' hw0 hIn0 hstd).symm
  have hyR : Expression.eval env.toEnvironment (shR inputVar 6).2
      = Expression.eval env0.toEnvironment (shR inputVar 6).2 := by
    rw [eval_shR_y inputVar env 6 pkX pkY digestLo digestHi r s fam hm hhint hw,
      eval_shR_y inputVar env0 6 pkX pkY digestLo digestHi r s vacuousFamily
        vacuousFamily_m hhint0' hw0]
    rfl
  have hRpt : Affine.Point.some (Expression.eval env.toEnvironment (shR inputVar 6).1)
        (Expression.eval env.toEnvironment (shR inputVar 6).2) hRnsE = Rpt0 := by
    rw [hRpt0]
    exact some_congr hxR hyR hRnsE hRnsE0
  have hdb : g.digestBits = g0.digestBits := by
    rw [hg, hg0, generateSeed_digestBits pkX pkY digestLo digestHi r s fam hm,
      generateSeed_digestBits pkX pkY digestLo digestHi r s vacuousFamily vacuousFamily_m]
  have hrb' : g.rBits = g0.rBits := by
    rw [hg, hg0, generateSeed_rBits pkX pkY digestLo digestHi r s fam hm,
      generateSeed_rBits pkX pkY digestLo digestHi r s vacuousFamily vacuousFamily_m]
  have hsb' : g.tBits = g0.tBits := by
    rw [hg, hg0, generateSeed_tBits pkX pkY digestLo digestHi r s fam hm,
      generateSeed_tBits pkX pkY digestLo digestHi r s vacuousFamily vacuousFamily_m]
  have hfam1 : famOf env.toEnvironment (fbEb inputVar 6) (fbRb inputVar 6)
        (fbSb inputVar 6)
        (Affine.Point.some (Expression.eval env.toEnvironment inputVar.pkX)
          (Expression.eval env.toEnvironment inputVar.pkY) hQnsE)
        (Affine.Point.some (Expression.eval env.toEnvironment (shR inputVar 6).1)
          (Expression.eval env.toEnvironment (shR inputVar 6).2) hRnsE)
      = famOf env.toEnvironment (fbEb inputVar 6) (fbRb inputVar 6)
        (fbSb inputVar 6) Qpt0 Rpt0 :=
    famOf_congr_pts env.toEnvironment _ _ _ hQpt hRpt
  have hfam2 : famOf env.toEnvironment (fbEb inputVar 6) (fbRb inputVar 6)
        (fbSb inputVar 6) Qpt0 Rpt0 = fam := by
    rw [hfamdef]
    exact main_famOf_eq inputVar 6 env0 env g0 g hhint0 hhint hw0 hw hdb hrb' hsb'
      Qpt0 Rpt0 Qpt0 Rpt0 rfl rfl
  have hfam := hfam1.trans hfam2
  have hH : (Seed.H g).IsOnCurve params :=
    generateSeed_H_onCurve pkX pkY digestLo digestHi r s fam hm
  have hgood : GoodOffset (Seed.H g) hH
      (famOf env.toEnvironment (fbEb inputVar 6) (fbRb inputVar 6)
        (fbSb inputVar 6)
        (Affine.Point.some (Expression.eval env.toEnvironment inputVar.pkX)
          (Expression.eval env.toEnvironment inputVar.pkY) hQnsE)
        (Affine.Point.some (Expression.eval env.toEnvironment (shR inputVar 6).1)
          (Expression.eval env.toEnvironment (shR inputVar 6).2) hRnsE)) := by
    rw [hfam]
    exact generateSeed_goodOffset pkX pkY digestLo digestHi r s fam hm hH
  have hHX : (Seed.H g).X
      = Expression.eval env.toEnvironment (seedPhase inputVar 6).1.hx :=
    (eval_seedPhase_hx inputVar g env 6 hhint hw).symm
  have hHY : (Seed.H g).Y
      = Expression.eval env.toEnvironment (seedPhase inputVar 6).1.hy :=
    (eval_seedPhase_hy inputVar g env 6 hhint hw).symm
  exact ⟨env, fam, hm, hhint, hw, hIn, Seed.H g, hH, hHX, hHY, hQnsE, hRnsE, hgood⟩

set_option linter.constructorNameAsVariable false in
/-- **The honest witness of a standard-valid input.** -/
theorem main_completeWitness_of_standard (pkX pkY digestLo digestHi r s : K)
    (hstd : standardVerify pkX pkY digestLo digestHi r s)
    (hlo : digestLo.val < 2 ^ 128) (hhi : digestHi.val < 2 ^ 128) :
    ∃ env : ProverEnvironment Fp,
      env.UsesLocalWitnessesCompleteness 6 ((main inputVar).operations 6) ∧
      CompleteWitness inputVar env 6 := by
  obtain ⟨env, fam, hm, hhint, hw, hIn, H, hH, hHX, hHY, hQnsE, hRnsE, hgood⟩ :=
    main_honestData pkX pkY digestLo digestHi r s hstd hlo hhi
  exact ⟨env, hw, CompleteWitness_of_ulwc inputVar env 6 pkX pkY digestLo digestHi r s fam hm
    hhint hw hIn hstd hlo hhi H hH hHX hHY hQnsE hRnsE hgood⟩

set_option linter.constructorNameAsVariable false in
/-- **Completeness for every standard-valid input.** -/
theorem main_completeness_of_standard (pkX pkY digestLo digestHi r s : K)
    (hstd : standardVerify pkX pkY digestLo digestHi r s)
    (hlo : digestLo.val < 2 ^ 128) (hhi : digestHi.val < 2 ^ 128) :
    ∃ env : ProverEnvironment Fp,
      ConstraintsHold.Completeness env ((main inputVar).operations 6) := by
  obtain ⟨env, hw, hcw⟩ :=
    main_completeWitness_of_standard pkX pkY digestLo digestHi r s hstd hlo hhi
  exact ⟨env, main_complete_with_seed inputVar env 6 hw hcw⟩

end StandardECDSA
