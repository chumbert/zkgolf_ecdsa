/-
# The honest witness satisfies `CompleteWitness` (task G2-c)

This module assembles the 30 fields of `CompleteWitness` for the concrete
environment built from `generateSeed`, from

* the environment's local witnesses (`UsesLocalWitnessesCompleteness`),
* the input embedding (`InputEmbedding`),
* the standard verification predicate, and
* a good offset for the *concrete* family `famOf` of the environment.

The offset fixed point is broken by `Witness/FamilyInvariance.lean`: the family
`famOf env …` depends only on the bit wires, which are `bitsOf r`, `bitsOf (n-s)`
and `bitsOf E` — independent of the offset.  So the honest prover may pick the
offset from a *reference* environment with the same bits.

No new axioms, no `native_decide`, no `sorry`.
-/
import StandardECDSA.Witness.HonestDigest
import StandardECDSA.Witness.HonestLadderDenominators
import StandardECDSA.Witness.HonestShiftedFields
import StandardECDSA.Witness.InputEmbedding
import StandardECDSA.Witness.FamilyInvariance
import StandardECDSA.Witness.HintBridge

namespace StandardECDSA

open Circuit
open StandardECDSA.Gadgets
open StandardECDSA.Phases
open StandardECDSA.Math
open StandardECDSA.Witness
open StandardECDSA.Math.FixedTables
open WeierstrassCurve

/-! ## The signature point `R` of the honest witness -/

/-- The circuit's `rx = r + n·overflow` expression evaluates to `stdVx`. -/
theorem eval_shR_x (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (pkX pkY digestLo digestHi r s : K) (fam : BadFamily Grp) (hm : fam.m < 1294)
    (hhint : env.hint = seedHint (generateSeed pkX pkY digestLo digestHi r s fam hm))
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hIn : InputEmbedding inp env pkX pkY digestLo digestHi r s)
    (hstd : standardVerify pkX pkY digestLo digestHi r s) :
    Expression.eval env.toEnvironment (shR inp n).1
      = stdVx pkX pkY digestLo digestHi r s := by
  set g := generateSeed pkX pkY digestLo digestHi r s fam hm with hg
  have hov := eval_seedPhase_overflow inp g env n hhint hw
  have hX : r + nFp * g.overflow = stdVx pkX pkY digestLo digestHi r s := by
    set ov := overflowOf (stdVx pkX pkY digestLo digestHi r s).val r.val with hovdef
    have h3 : g.overflow = ((ov : Nat) : K) := by
      rw [hovdef]; simp only [hg, generateSeed, stdVx]
    have h4 : r + nFp * ((ov : Nat) : K) = ((r.val + StandardECDSA.n * ov : Nat) : K) := by
      have hr : r = ((r.val : Nat) : K) := (ZMod.natCast_zmod_val r).symm
      have hn : nFp = ((StandardECDSA.n : Nat) : K) := by simp only [nFp]
      conv_lhs => rw [hr, hn]
      rw [← Nat.cast_mul, ← Nat.cast_add]
    rw [h3, h4, hovdef, ← generateSeed_overflow pkX pkY digestLo digestHi r s hstd,
      ZMod.natCast_zmod_val]
  simp only [shR, eval_add', eval_sc', hov, hIn.2.2.2.2.1]
  exact hX

/-- The circuit's `ry` expression evaluates to the seed's `ry`. -/
theorem eval_shR_y (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (pkX pkY digestLo digestHi r s : K) (fam : BadFamily Grp) (hm : fam.m < 1294)
    (hhint : env.hint = seedHint (generateSeed pkX pkY digestLo digestHi r s fam hm))
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    Expression.eval env.toEnvironment (shR inp n).2
      = (generateSeed pkX pkY digestLo digestHi r s fam hm).ry := by
  simp only [shR]
  exact eval_seedPhase_ry inp _ env n hhint hw

/-- The signature point `R` of the honest witness is on the curve. -/
theorem hRns_of_generateSeed (pkX pkY digestLo digestHi r s : K)
    (fam : BadFamily Grp) (hm : fam.m < 1294)
    (hstd : standardVerify pkX pkY digestLo digestHi r s) :
    NS (affinePt (stdV { X := pkX, Y := pkY } r s (digestOf digestLo digestHi))).X
      (affinePt (stdV { X := pkX, Y := pkY } r s (digestOf digestLo digestHi))).Y :=
  nsOfOnCurve _ (generateSeed_R_onCurve pkX pkY digestLo digestHi r s fam hm hstd)

set_option linter.constructorNameAsVariable false in
/-- The shifted-table denominators of `main`, isolated so that the defeq checks
against `CompleteWitness`'s field types stay inside their own heartbeat budget. -/
theorem main_shifted_denominators (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
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
    Expression.eval env (seedPhase inp n).1.hy ≠ 0 ∧
    (Expression.eval env (seedPhase inp n).1.hx - env.get (off7 inp n + 2) ≠ 0) ∧
    (Expression.eval env inp.pkX - env.get (off7 inp n + 6) ≠ 0) ∧
    (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow)
      - env.get (off7 inp n + 6) ≠ 0) ∧
    (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow)
      - env.get (off7 inp n + 10) ≠ 0) ∧
    (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow)
      - env.get (off7 inp n + 22) ≠ 0) := by
  classical
  set Qpt : Affine.Point Wp := Affine.Point.some (Expression.eval env.toEnvironment inp.pkX)
    (Expression.eval env.toEnvironment inp.pkY) hQnsE with hQptdef
  set Rpt : Affine.Point Wp := Affine.Point.some (Expression.eval env.toEnvironment (shR inp n).1)
    (Expression.eval env.toEnvironment (shR inp n).2) hRnsE with hRptdef
  exact ⟨hshy_of_ulwc inp env n H hH Qpt Rpt hHX hHY hQnsE rfl hRnsE rfl hgood hw,
    hs1_of_ulwc inp env n H hH Qpt Rpt hHX hHY hQnsE rfl hRnsE rfl hgood hw,
    hs2_of_ulwc inp env n H hH Qpt Rpt hHX hHY hQnsE rfl hRnsE rfl hgood hw,
    hs3_of_ulwc inp env n H hH Qpt Rpt hHX hHY hQnsE rfl hRnsE rfl hgood hw,
    hs4_of_ulwc inp env n H hH Qpt Rpt hHX hHY hQnsE rfl hRnsE rfl hgood hw,
    hs5_of_ulwc inp env n H hH Qpt Rpt hHX hHY hQnsE rfl hRnsE rfl hgood hw⟩

/-! ## The honest witness satisfies `CompleteWitness` -/

/-- The six ladder fields of `CompleteWitness`, verbatim. -/
structure LadderWitness (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat) : Prop where
  hj1 : ∀ j : Fin 255,
    Expression.eval env.toEnvironment
        ((mux4W ((bitsPhase (off3 inp n)).1.rb.get ⟨255 - j.val, by omega⟩)
          ((bitsPhase (off3 inp n)).1.sb.get ⟨255 - j.val, by omega⟩)
          ((shiftedTables ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy) (inp.pkX, inp.pkY)
            (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry)
            (off7 inp n)).1.x0 j.val)
          ((shiftedTables ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy) (inp.pkX, inp.pkY)
            (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry)
            (off7 inp n)).1.x1 j.val)
          ((shiftedTables ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy) (inp.pkX, inp.pkY)
            (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry)
            (off7 inp n)).1.x2 j.val)
          ((shiftedTables ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy) (inp.pkX, inp.pkY)
            (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry)
            (off7 inp n)).1.x3 j.val)).output (off8 inp n + j.val * 12)).1
      - Expression.eval env.toEnvironment
        (jlAcc ((seedPhase inp n).1.hx, -(seedPhase inp n).1.hy)
          (shiftedTables ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy) (inp.pkX, inp.pkY)
            (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry)
            (off7 inp n)).1
          (bitsPhase (off3 inp n)).1.rb (bitsPhase (off3 inp n)).1.sb (off8 inp n) j).1 ≠ 0
  hj2 : ∀ j : Fin 255,
    Expression.eval env.toEnvironment
        (jlAcc ((seedPhase inp n).1.hx, -(seedPhase inp n).1.hy)
          (shiftedTables ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy) (inp.pkX, inp.pkY)
            (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry)
            (off7 inp n)).1
          (bitsPhase (off3 inp n)).1.rb (bitsPhase (off3 inp n)).1.sb (off8 inp n) j).1
      - env.get (off8 inp n + j.val * 12 + 6 + 2) ≠ 0
  hjf1 : Expression.eval env.toEnvironment
      ((mux4W ((bitsPhase (off3 inp n)).1.rb.get ⟨0, by omega⟩)
        ((bitsPhase (off3 inp n)).1.sb.get ⟨0, by omega⟩)
        ((shiftedTables ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy) (inp.pkX, inp.pkY)
          (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry)
          (off7 inp n)).1.x0 255)
        ((shiftedTables ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy) (inp.pkX, inp.pkY)
          (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry)
          (off7 inp n)).1.x1 255)
        ((shiftedTables ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy) (inp.pkX, inp.pkY)
          (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry)
          (off7 inp n)).1.x2 255)
        ((shiftedTables ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy) (inp.pkX, inp.pkY)
          (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry)
          (off7 inp n)).1.x3 255)).output (off8 inp n + 3060)).1
    - Expression.eval env.toEnvironment
      (jlOut ((seedPhase inp n).1.hx, -(seedPhase inp n).1.hy)
        (shiftedTables ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy) (inp.pkX, inp.pkY)
          (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry)
          (off7 inp n)).1
        (bitsPhase (off3 inp n)).1.rb (bitsPhase (off3 inp n)).1.sb (off8 inp n)).1 ≠ 0
  hjf2 : Expression.eval env.toEnvironment
      (jlOut ((seedPhase inp n).1.hx, -(seedPhase inp n).1.hy)
        (shiftedTables ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy) (inp.pkX, inp.pkY)
          (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry)
          (off7 inp n)).1
        (bitsPhase (off3 inp n)).1.rb (bitsPhase (off3 inp n)).1.sb (off8 inp n)).1
    - env.get (off8 inp n + 3060 + 6 + 2) ≠ 0
  hjf3 : env.get (off8 inp n + 3060 + 6 + 3) * env.get (off8 inp n + 3060 + 6 + 3)
    - Expression.eval env.toEnvironment
      (jlOut ((seedPhase inp n).1.hx, -(seedPhase inp n).1.hy)
        (shiftedTables ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy) (inp.pkX, inp.pkY)
          (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry)
          (off7 inp n)).1
        (bitsPhase (off3 inp n)).1.rb (bitsPhase (off3 inp n)).1.sb (off8 inp n)).1
    - env.get (off8 inp n + 3060 + 6 + 2)
    - Expression.eval env.toEnvironment
      (((fixedBase ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy)
          (bitsPhase (off3 inp n)).1.eb (off6 inp n)).1).1) = 0
  hjf4 : env.get (off8 inp n + 3060 + 6 + 3) *
      (Expression.eval env.toEnvironment
        (jlOut ((seedPhase inp n).1.hx, -(seedPhase inp n).1.hy)
          (shiftedTables ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy) (inp.pkX, inp.pkY)
            (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry)
            (off7 inp n)).1
          (bitsPhase (off3 inp n)).1.rb (bitsPhase (off3 inp n)).1.sb (off8 inp n)).1
        - Expression.eval env.toEnvironment
          (((fixedBase ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy)
              (bitsPhase (off3 inp n)).1.eb (off6 inp n)).1).1))
    - Expression.eval env.toEnvironment
      (jlOut ((seedPhase inp n).1.hx, -(seedPhase inp n).1.hy)
        (shiftedTables ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy) (inp.pkX, inp.pkY)
          (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry)
          (off7 inp n)).1
        (bitsPhase (off3 inp n)).1.rb (bitsPhase (off3 inp n)).1.sb (off8 inp n)).2
    - Expression.eval env.toEnvironment
      (-(((fixedBase ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy)
          (bitsPhase (off3 inp n)).1.eb (off6 inp n)).1).2)) = 0


set_option linter.constructorNameAsVariable false in
/-- **`CompleteWitness` for the honest environment.**  All 30 fields follow from
the environment's local witnesses, the input embedding, standard validity and a
good offset for the concrete family `famOf`. -/
theorem CompleteWitness_of_ulwc_core (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
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
        (Expression.eval env.toEnvironment (shR inp n).2) hRnsE)))
    (hL : LadderWitness inp env n) :
    CompleteWitness inp env n := by
  classical
  set g := generateSeed pkX pkY digestLo digestHi r s fam hm with hg
  have hsc : ScalarFacts g (digestOf digestLo digestHi) r.val (StandardECDSA.n - s.val) :=
    generateSeed_scalarFacts pkX pkY digestLo digestHi r s fam hm hstd.2.2.1 hstd.2.2.2.1 hlo hhi
  set rx := (stdVx pkX pkY digestLo digestHi r s).val with hrx
  set Qpt : Affine.Point Wp := Affine.Point.some (Expression.eval env.toEnvironment inp.pkX)
    (Expression.eval env.toEnvironment inp.pkY) hQnsE with hQptdef
  set Rpt : Affine.Point Wp := Affine.Point.some (Expression.eval env.toEnvironment (shR inp n).1)
    (Expression.eval env.toEnvironment (shR inp n).2) hRnsE with hRptdef
  -- the bit-wire Boolean-ness
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
  -- the fixed-base denominators and spec
  have hdx0 := hfb0_of_ulwc inp env n H hH Qpt Rpt hHX hgood
  have hfb := hfb_of_ulwc inp env n H hH Qpt Rpt hHX hHY hgood hw hbE hdx0
  have hd0v := hd0_of_ulwc inp g env n _ _ _ digestLo digestHi hhint hw hsc hIn.2.2.1 rfl hlo
  have hd1v := hd1_of_ulwc inp g env n _ _ _ digestLo digestHi hhint hw hsc hIn.2.2.2.1 rfl hlo hhi
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
  have hovv : Expression.eval env.toEnvironment (seedPhase inp n).1.overflow
      = ((overflowOf (stdVx pkX pkY digestLo digestHi r s).val r.val : Nat) : K) := by
    rw [eval_seedPhase_overflow inp g env n hhint hw]
    exact generateSeed_overflow_val pkX pkY digestLo digestHi r s fam hm
  have hlegv : Expression.eval env.toEnvironment (seedPhase inp n).1.overflow = 1 →
      prefVal (fun j => aNatOf (fun k => Expression.eval env.toEnvironment
        ((bitsPhase (off3 inp n)).1.rb.getD k (cst 0))) (255 - j)) 256 ≤ pSubNSubOne :=
    hleg_of_ulwc inp g env n (digestOf digestLo digestHi) r.val
      (StandardECDSA.n - s.val) rx hhint hw hsc
      hovv (by rw [hrx]; exact generateSeed_overflow pkX pkY digestLo digestHi r s hstd)
      (by rw [hrx]; exact ZMod.val_lt _)
  have htlt : StandardECDSA.n - s.val < StandardECDSA.n := by
    have hn0 : 0 < StandardECDSA.n := by decide
    exact Nat.sub_lt hn0 hstd.2.2.2.1
  obtain ⟨hshyV, hs1V, hs2V, hs3V, hs4V, hs5V⟩ :=
    main_shifted_denominators inp env n pkX pkY digestLo digestHi r s fam hm hhint hw hIn
      hstd hlo hhi H hH hHX hHY hQnsE hRnsE hgood
  refine
    { hov := ?_, hQ := ?_, hR := ?_, hH := ?_, hr := ?_, ht := ?_
      hb := ?_, hb' := ?_, hb'' := ?_
      hd0 := ?_, hd1 := ?_, hd2 := ?_, hd3 := ?_
      hle := ?_, hle' := ?_, hleg := ?_
      hfb0 := ?_, hfb := ?_
      hshy := hshyV, hs1 := hs1V, hs2 := hs2V, hs3 := hs3V, hs4 := hs4V, hs5 := hs5V
      hj1 := hL.hj1, hj2 := hL.hj2, hjf1 := hL.hjf1, hjf2 := hL.hjf2
      hjf3 := hL.hjf3, hjf4 := hL.hjf4 }
  · exact hov_of_ulwc inp g env n _ _ _ hhint hw hsc
  · exact hQ_of_embedding inp env pkX pkY digestLo digestHi r s hIn hstd
  · exact hR_of_generateSeed inp env n pkX pkY digestLo digestHi r s fam hm hhint hw hIn hstd
  · exact hH_of_ulwc inp g env n hhint hw
      (generateSeed_H_onCurve pkX pkY digestLo digestHi r s fam hm)
  · exact hr_of_embedding inp env pkX pkY digestLo digestHi r s hIn hstd
  · exact ht_of_embedding inp env pkX pkY digestLo digestHi r s hIn hstd
  · exact hb_of_ulwc inp g env n _ _ _ hhint hw hsc
  · exact hbR_of_ulwc inp g env n _ _ _ hhint hw hsc
  · exact hbT_of_ulwc inp g env n _ _ _ hhint hw hsc
  · exact hd0v
  · exact hd1v
  · exact hd2_of_ulwc inp g env n (digestOf digestLo digestHi) r.val
      (StandardECDSA.n - s.val) hhint hw hsc
      (hIn.2.2.2.2.1.trans (ZMod.natCast_zmod_val r).symm) hstd.2.2.1
  · exact hd3_of_ulwc inp g env n (digestOf digestLo digestHi) r.val
      (StandardECDSA.n - s.val) s hhint hw hsc hIn.2.2.2.2.2 hstd.2.2.2.2.1 rfl
  · exact hle_of_ulwc inp g env n (digestOf digestLo digestHi) r.val
      (StandardECDSA.n - s.val) hhint hw hsc hstd.2.2.1
  · exact hle'_of_ulwc inp g env n (digestOf digestLo digestHi) r.val
      (StandardECDSA.n - s.val) hhint hw hsc htlt
  · exact hlegv
  · exact hdx0
  · exact hfb

end StandardECDSA
