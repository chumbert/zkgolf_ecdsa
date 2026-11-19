/-
# Honest-witness denominators (task G2-b, fixed-base part)

`CompleteWitness` (`StandardECDSA/Main.lean`) carries the fixed-base
denominators `hfb0` (the initial shift addition) and `hfb` (the 128 windows) as
explicit hypotheses.  This module discharges them from the circuit rows.

The key ingredient is `fixedBase_fbInv`: the prefix invariant `fbInv` holds at
*every* window boundary `k < 128`, not just at the end.  `fixedBase_spec`
(`Phases/FixedBaseSemantics.lean`) only extracts the `k = 128` instance; the
per-window instance is what `fbWin_dx` consumes.

Every proof is complete; no new axioms and no `native_decide`.
-/

import StandardECDSA.Main
import StandardECDSA.Witness.HintBridge
import StandardECDSA.Phases.HonestDenominators
import StandardECDSA.Phases.HonestWitness

namespace StandardECDSA.Phases

open WeierstrassCurve StandardECDSA StandardECDSA.Gadgets StandardECDSA.Math
open StandardECDSA.Math.FixedTables

/-! ## The prefix invariant at every window boundary -/

/-- `fbAcc` written with `Circuit.output` instead of the raw `.1` projection. -/
theorem fbAcc_eq' (eb : Vector E 256) (h : Pt) (n : Nat) (i : Fin 128) :
    fbAcc eb h n i = Circuit.FoldlM.foldlAcc (n + 4) (Vector.finRange 128)
      (fixedBaseBody eb fixedTables) ((affAdd h (cst shiftX, cst (-shiftY))).output n) i := by
  rw [fbAcc_eq]

/-- **The fixed-base prefix invariant holds at every window boundary.**

This is the per-window form of the induction inside `fixedBase_spec`: the
accumulator after `k` windows represents `H - S + [winSum k]G`. -/
theorem fixedBase_fbInv (env : Environment Fp) (h : Pt) (eb : Vector E 256)
    (Hpt : Affine.Point Wp) (n : Nat)
    (hH : NS (Expression.eval env h.1) (Expression.eval env h.2))
    (hHpt : Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH = Hpt)
    (hb : ∀ k : Fin 256,
      Expression.eval env (eb.get k) = 0 ∨ Expression.eval env (eb.get k) = 1)
    (hdx0 : Expression.eval env (cst shiftX) - Expression.eval env h.1 ≠ 0)
    (hdx : ∀ (k : Nat) (hk : k < 128),
      Expression.eval env ((fbMux eb fixedTables ⟨k, hk⟩).output (n + 4 + k * 5)).1
        - Expression.eval env (Circuit.FoldlM.foldlAcc (n + 4) (Vector.finRange 128)
            (fixedBaseBody eb fixedTables)
            ((affAdd h (cst shiftX, cst (-shiftY))).output n) ⟨k, hk⟩).1 ≠ 0)
    (hc : ConstraintsHold.Soundness env ((fixedBase h eb).operations n)) :
    ∀ (k : Nat) (hk : k < 128), fbInv env eb Hpt k (fbAcc eb h n ⟨k, hk⟩) := by
  -- the shift point is finite and is `shiftPt`
  have hS : NS shiftX shiftY :=
    ns_congr shiftX_eq shiftY_eq
      (affine_ns (mulG shiftNat) (mulG_on_curve shiftNat)
        (mulG_Z_ne_zero_gen shiftNat shiftNat_mod_ne_zero))
  have hshiftPt : Affine.Point.some shiftX shiftY hS = shiftPt :=
    (some_congr shiftX_eq shiftY_eq hS
      (affine_ns (mulG shiftNat) (mulG_on_curve shiftNat)
        (mulG_Z_ne_zero_gen shiftNat shiftNat_mod_ne_zero))).trans fixedShift_some
  have hB : NS (Expression.eval env (cst shiftX)) (Expression.eval env (cst (-shiftY))) :=
    negPt_ns hS
  have hneg : Affine.Point.some (Expression.eval env (cst shiftX))
      (Expression.eval env (cst (-shiftY))) hB = -shiftPt := by
    have h := negPt_group shiftX shiftY hS
    rw [hshiftPt] at h
    exact h
  -- split the phase into the initial addition and the 128-window fold
  have hc' : ConstraintsHold.Soundness env
      ((affAdd h (cst shiftX, cst (-shiftY))).operations n
        ++ (Circuit.foldlRange 128 ((affAdd h (cst shiftX, cst (-shiftY))).output n)
              (fixedBaseBody eb fixedTables)
              (fixedBaseBody_constantLength eb fixedTables)).operations (n + 4)) := hc
  obtain ⟨hc1, hc2⟩ := soundness_append_foldlRange env
    ((affAdd h (cst shiftX, cst (-shiftY))).operations n) hc'
  -- the initial addition
  have hout0 : (affAdd h (cst shiftX, cst (-shiftY))).output n
      = (Expression.var (F := Fp) ⟨n + 2⟩, Expression.var (F := Fp) ⟨n + 3⟩) := by
    simp only [affAdd_output]
  have hcl : ∀ (i : Fin 128),
      (fixedBaseBody eb fixedTables default i).localLength = 5 := fun i =>
    (fixedBaseBody_constantLength eb fixedTables).localLength_eq (default, i) 0
  have hinit : fbInv env eb Hpt 0 ((affAdd h (cst shiftX, cst (-shiftY))).output n) := by
    rw [hout0]
    obtain ⟨hR0, hR0val⟩ :=
      affAdd_sound env h (cst shiftX, cst (-shiftY)) n hH hB hdx0 hc1
    refine ⟨hR0, hR0val.trans ?_⟩
    rw [hneg, hHpt]
    simp only [winSum, Finset.range_zero, Finset.sum_empty, zero_nsmul,
      toAffineLift_zero, add_zero]
  -- one window preserves the invariant
  have hstep : ∀ (j : Nat) (hj : j < 128),
      fbInv env eb Hpt j (Fin.foldl j (fun acc (i : Fin j) =>
        (fixedBaseBody eb fixedTables acc ⟨i.val, by omega⟩).output (n + 4 + i.val * 5))
        ((affAdd h (cst shiftX, cst (-shiftY))).output n)) →
      fbInv env eb Hpt (j + 1) ((fixedBaseBody eb fixedTables
        (Fin.foldl j (fun acc (i : Fin j) =>
          (fixedBaseBody eb fixedTables acc ⟨i.val, by omega⟩).output (n + 4 + i.val * 5))
          ((affAdd h (cst shiftX, cst (-shiftY))).output n)) ⟨j, hj⟩).output
        (n + 4 + j * 5)) := by
    intro j hj hacc
    have hcj := hc2 ⟨j, hj⟩
    rw [hcl ⟨j, hj⟩] at hcj
    rw [foldlAcc_eq env eb fixedTables ((affAdd h (cst shiftX, cst (-shiftY))).output n)
      (n + 4) j hj] at hcj
    have hdxj := hdx j hj
    rw [foldlAcc_eq env eb fixedTables ((affAdd h (cst shiftX, cst (-shiftY))).output n)
      (n + 4) j hj] at hdxj
    exact fbStep env eb Hpt (n + 4) j hj _ (hb ⟨2 * j, by omega⟩)
      (hb ⟨2 * j + 1, by omega⟩) hdxj hacc hcj
  -- run the induction
  have hP := fin_foldl_inv' (fun acc (i : Fin 128) =>
      (fixedBaseBody eb fixedTables acc i).output (n + 4 + i.val * 5))
    ((affAdd h (cst shiftX, cst (-shiftY))).output n)
    (fun k acc => fbInv env eb Hpt k acc) hinit hstep
  intro k hk
  rw [fbAcc_eq,
    foldlAcc_eq env eb fixedTables ((affAdd h (cst shiftX, cst (-shiftY)) n).1) (n + 4) k hk]
  exact hP k (by omega)



/-! ## The stage abbreviations of `main` -/

/-- The digest-bit vector of `main`. -/
abbrev fbEb (inp : Var Input Fp) (n : Nat) : Vector E 256 := (bitsPhase (off3 inp n)).1.eb

/-- The `r`-bit vector of `main`. -/
abbrev fbRb (inp : Var Input Fp) (n : Nat) : Vector E 256 := (bitsPhase (off3 inp n)).1.rb

/-- The `n - s`-bit vector of `main`. -/
abbrev fbSb (inp : Var Input Fp) (n : Nat) : Vector E 256 := (bitsPhase (off3 inp n)).1.sb

/-- The offset point `H` of `main`, as a pair of expressions. -/
abbrev fbH (inp : Var Input Fp) (n : Nat) : Pt :=
  ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy)

/-! ## Extracting the fixed-base stage of `main` -/

/-- The fixed-base stage of `main` inherits `main`'s local witnesses. -/
theorem main_ulwc_fixedBase (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (h : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    env.UsesLocalWitnessesCompleteness (off6 inp n)
      ((fixedBase ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy)
        (bitsPhase (off3 inp n)).1.eb (off6 inp n)).2) := by
  rw [main_ops'] at h
  simp only [List.append_assoc] at h
  obtain ⟨-, h⟩ := ulwc_append_left h
  obtain ⟨-, h⟩ := ulwc_append_left h
  obtain ⟨-, h⟩ := ulwc_append_left h
  obtain ⟨-, h⟩ := ulwc_append_left h
  obtain ⟨-, h⟩ := ulwc_append_left h
  obtain ⟨-, h⟩ := ulwc_append_left h
  obtain ⟨h7, -⟩ := ulwc_append_left h
  exact h7

/-! ## Phase-level soundness from local witnesses -/

/-- The fixed-base phase's rows hold for the honest witness. -/
theorem fixedBase_soundness_of_ulwc (h : Pt) (eb : Vector E 256)
    (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((fixedBase h eb).operations n))
    (hdx0 : Expression.eval env.toEnvironment (cst shiftX)
      - Expression.eval env.toEnvironment h.1 ≠ 0)
    (hdx : ∀ i : Fin 128,
      Expression.eval env.toEnvironment (fbMux eb fixedTables i (n + 4 + i.val * 5)).1.1
        - Expression.eval env.toEnvironment (fbAcc eb h n i).1 ≠ 0) :
    ConstraintsHold.Soundness env ((fixedBase h eb).operations n) := by
  rw [fixedBase_ops] at hw ⊢
  rw [ulwc_append] at hw
  simp only [affAdd_localLength'] at hw
  simp only [ConstraintsHold.Soundness, Operations.forAllNoOffset_append]
  refine ⟨affAdd_soundness_of_ulwc h (cst shiftX, cst (-shiftY)) env n hw.1 hdx0, ?_⟩
  rw [Circuit.foldlRange.forAllNoOffset]
  rw [Circuit.foldlRange.usesLocalWitnesses] at hw
  intro i
  simp only [fixedBaseBody_localLength] at hw ⊢
  simp only [← fbAcc_eq'] at hw ⊢
  simp only [fixedBaseBody_eq, circuit_norm, ulwc_append] at hw
  exact fixedBaseBody_soundness_of_ulwc eb (fbAcc eb h n i) i env (n + 4 + i.val * 5)
    (hw.2 i).1 (hw.2 i).2 (hdx i)

/-! ## The joint induction: invariant + denominators from the circuit rows -/

set_option linter.constructorNameAsVariable false in
/-- **The fixed-base prefix invariant at every window boundary, from the rows.**

Unlike `fixedBase_fbInv`, this does not take the denominators as hypotheses: at
each window the invariant supplies the group image that `fbWin_dx` needs, and
`fbWin_dx` supplies the denominator that the window's soundness needs. -/
theorem fixedBase_fbInv_of_ulwc (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (H : AffinePoint K) (hH : H.IsOnCurve params) (Qpt Rpt : Affine.Point Wp)
    (hHX : H.X = Expression.eval env.toEnvironment (seedPhase inp n).1.hx)
    (hHY : H.Y = Expression.eval env.toEnvironment (seedPhase inp n).1.hy)
    (hgood : GoodOffset H hH (famOf env.toEnvironment (fbEb inp n) (fbRb inp n) (fbSb inp n)
      Qpt Rpt))
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hb : ∀ k : Fin 256,
      Expression.eval env.toEnvironment ((fbEb inp n).get k) = 0 ∨
        Expression.eval env.toEnvironment ((fbEb inp n).get k) = 1)
    (hdx0 : Expression.eval env.toEnvironment (cst shiftX)
      - Expression.eval env.toEnvironment (seedPhase inp n).1.hx ≠ 0) :
    ∀ i : Fin 128,
      fbInv env.toEnvironment (fbEb inp n) (goodOffsetAffinePt H hH) i.val
        (fbAcc (fbEb inp n) (fbH inp n) (off6 inp n) i) := by
  -- the fixed-base stage's local witnesses
  have hwfb := main_ulwc_fixedBase inp env n hw
  change env.UsesLocalWitnessesCompleteness (off6 inp n)
    ((fixedBase (fbH inp n) (fbEb inp n)).operations (off6 inp n)) at hwfb
  rw [fixedBase_ops] at hwfb
  rw [ulwc_append] at hwfb
  simp only [affAdd_localLength'] at hwfb
  obtain ⟨hw0, hwfold⟩ := hwfb
  rw [Circuit.foldlRange.usesLocalWitnesses] at hwfold
  -- the per-window local witnesses, in `Fin.foldl` form
  have hwin : ∀ (j : Nat) (hj : j < 128),
      env.UsesLocalWitnessesCompleteness (off6 inp n + 4 + j * 5)
        ((fixedBaseBody (fbEb inp n) fixedTables
          (Fin.foldl j (fun acc (i : Fin j) =>
            (fixedBaseBody (fbEb inp n) fixedTables acc ⟨i.val, by omega⟩).output
              (off6 inp n + 4 + i.val * 5))
          ((affAdd (fbH inp n) (cst shiftX, cst (-shiftY))).output (off6 inp n))) ⟨j, hj⟩).operations
          (off6 inp n + 4 + j * 5)) := by
    intro j hj
    have h := hwfold ⟨j, hj⟩
    simp only [fixedBaseBody_localLength] at h
    rw [foldlAcc_eq env.toEnvironment (fbEb inp n) fixedTables
      ((affAdd (fbH inp n) (cst shiftX, cst (-shiftY))).output (off6 inp n)) (off6 inp n + 4) j hj]
      at h
    exact h
  -- the initial invariant
  have hHns : NS (Expression.eval env.toEnvironment (fbH inp n).1)
      (Expression.eval env.toEnvironment (fbH inp n).2) := by
    rw [← hHX, ← hHY]
    exact nsOfOnCurve H hH
  have hHpt : Affine.Point.some (Expression.eval env.toEnvironment (fbH inp n).1)
      (Expression.eval env.toEnvironment (fbH inp n).2) hHns = goodOffsetAffinePt H hH := by
    rw [goodOffsetAffinePt_eq_some H hH hgood]
    exact some_congr hHX.symm hHY.symm hHns (nsOfOnCurve H hH)
  have hS : NS shiftX shiftY :=
    ns_congr shiftX_eq shiftY_eq
      (affine_ns (mulG shiftNat) (mulG_on_curve shiftNat)
        (mulG_Z_ne_zero_gen shiftNat shiftNat_mod_ne_zero))
  have hshiftPt : Affine.Point.some shiftX shiftY hS = shiftPt :=
    (some_congr shiftX_eq shiftY_eq hS
      (affine_ns (mulG shiftNat) (mulG_on_curve shiftNat)
        (mulG_Z_ne_zero_gen shiftNat shiftNat_mod_ne_zero))).trans fixedShift_some
  have hB : NS (Expression.eval env.toEnvironment (cst shiftX))
      (Expression.eval env.toEnvironment (cst (-shiftY))) := negPt_ns hS
  have hneg : Affine.Point.some (Expression.eval env.toEnvironment (cst shiftX))
      (Expression.eval env.toEnvironment (cst (-shiftY))) hB = -shiftPt := by
    have h := negPt_group shiftX shiftY hS
    rw [hshiftPt] at h
    exact h
  have hinit : fbInv env.toEnvironment (fbEb inp n) (goodOffsetAffinePt H hH) 0
      ((affAdd (fbH inp n) (cst shiftX, cst (-shiftY))).output (off6 inp n)) := by
    have hout0 : (affAdd (fbH inp n) (cst shiftX, cst (-shiftY))).output (off6 inp n)
        = (Expression.var (F := Fp) ⟨off6 inp n + 2⟩,
            Expression.var (F := Fp) ⟨off6 inp n + 3⟩) := by
      simp only [affAdd_output]
    rw [hout0]
    obtain ⟨hR0, hR0val⟩ :=
      affAdd_sound env.toEnvironment (fbH inp n) (cst shiftX, cst (-shiftY)) (off6 inp n)
        hHns hB hdx0
        (affAdd_soundness_of_ulwc (fbH inp n) (cst shiftX, cst (-shiftY)) env (off6 inp n)
          hw0 hdx0)
    refine ⟨hR0, hR0val.trans ?_⟩
    rw [hneg, hHpt]
    simp only [winSum, Finset.range_zero, Finset.sum_empty, zero_nsmul,
      toAffineLift_zero, add_zero]
  -- one window preserves the invariant
  have hstep : ∀ (j : Nat) (hj : j < 128),
      fbInv env.toEnvironment (fbEb inp n) (goodOffsetAffinePt H hH) j
        (Fin.foldl j (fun acc (i : Fin j) =>
          (fixedBaseBody (fbEb inp n) fixedTables acc ⟨i.val, by omega⟩).output
            (off6 inp n + 4 + i.val * 5))
          ((affAdd (fbH inp n) (cst shiftX, cst (-shiftY))).output (off6 inp n))) →
      fbInv env.toEnvironment (fbEb inp n) (goodOffsetAffinePt H hH) (j + 1)
        ((fixedBaseBody (fbEb inp n) fixedTables
          (Fin.foldl j (fun acc (i : Fin j) =>
            (fixedBaseBody (fbEb inp n) fixedTables acc ⟨i.val, by omega⟩).output
              (off6 inp n + 4 + i.val * 5))
            ((affAdd (fbH inp n) (cst shiftX, cst (-shiftY))).output (off6 inp n))) ⟨j, hj⟩).output
          (off6 inp n + 4 + j * 5)) := by
    intro j hj hacc
    have hwj := hwin j hj
    simp only [fixedBaseBody_eq, circuit_norm, ulwc_append] at hwj
    have hrow : Expression.eval env.toEnvironment
        (pm ((fbEb inp n).get ⟨2 * j, by omega⟩) ((fbEb inp n).get ⟨2 * j + 1, by omega⟩)
          - Expression.var (F := Fp) ⟨off6 inp n + 4 + j * 5⟩) = 0 := by
      have hc1 := muxConst4W_soundness_of_ulwc ((fbEb inp n).get ⟨2 * j, by omega⟩)
        ((fbEb inp n).get ⟨2 * j + 1, by omega⟩) (fixedTables.getD j #[]) env
        (off6 inp n + 4 + j * 5) hwj.1
      simp only [fixedTables_getD_row j hj, muxConst4W, circuit_norm] at hc1
      simpa only [circuit_norm] using hc1
    have hdx := fbWin_dx env.toEnvironment (fbEb inp n) (fbRb inp n) (fbSb inp n) Qpt Rpt
      H hH hgood (off6 inp n + 4) j hj _ (hb ⟨2 * j, by omega⟩)
      (hb ⟨2 * j + 1, by omega⟩) hrow hacc
    have hc := fixedBaseBody_soundness_of_ulwc (fbEb inp n) _ ⟨j, hj⟩ env
      (off6 inp n + 4 + j * 5) hwj.1 hwj.2 hdx
    exact fbStep env.toEnvironment (fbEb inp n) (goodOffsetAffinePt H hH) (off6 inp n + 4)
      j hj _ (hb ⟨2 * j, by omega⟩) (hb ⟨2 * j + 1, by omega⟩) hdx hacc hc
  have hP := fin_foldl_inv' (fun acc (i : Fin 128) =>
      (fixedBaseBody (fbEb inp n) fixedTables acc i).output (off6 inp n + 4 + i.val * 5))
    ((affAdd (fbH inp n) (cst shiftX, cst (-shiftY))).output (off6 inp n))
    (fun k acc => fbInv env.toEnvironment (fbEb inp n) (goodOffsetAffinePt H hH) k acc)
    hinit hstep
  intro i
  rw [fbAcc_eq',
    foldlAcc_eq env.toEnvironment (fbEb inp n) fixedTables
      ((affAdd (fbH inp n) (cst shiftX, cst (-shiftY))).output (off6 inp n)) (off6 inp n + 4)
      i.val i.isLt]
  exact hP i.val (by omega)

set_option linter.constructorNameAsVariable false in
/-- **The 128 fixed-base window denominators of `main` do not vanish.** -/
theorem hfb_of_ulwc (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (H : AffinePoint K) (hH : H.IsOnCurve params) (Qpt Rpt : Affine.Point Wp)
    (hHX : H.X = Expression.eval env.toEnvironment (seedPhase inp n).1.hx)
    (hHY : H.Y = Expression.eval env.toEnvironment (seedPhase inp n).1.hy)
    (hgood : GoodOffset H hH (famOf env.toEnvironment (fbEb inp n) (fbRb inp n) (fbSb inp n)
      Qpt Rpt))
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hb : ∀ k : Fin 256,
      Expression.eval env.toEnvironment ((fbEb inp n).get k) = 0 ∨
        Expression.eval env.toEnvironment ((fbEb inp n).get k) = 1)
    (hdx0 : Expression.eval env.toEnvironment (cst shiftX)
      - Expression.eval env.toEnvironment (seedPhase inp n).1.hx ≠ 0) :
    ∀ i : Fin 128,
      Expression.eval env.toEnvironment
          (fbMux (fbEb inp n) StandardECDSA.Math.FixedTables.fixedTables i
            (off6 inp n + 4 + i.val * 5)).1.1
        - Expression.eval env.toEnvironment
          (fbAcc (fbEb inp n) (fbH inp n) (off6 inp n) i).1 ≠ 0 := by
  intro i
  -- the window's local witnesses
  have hwfb := main_ulwc_fixedBase inp env n hw
  change env.UsesLocalWitnessesCompleteness (off6 inp n)
    ((fixedBase (fbH inp n) (fbEb inp n)).operations (off6 inp n)) at hwfb
  rw [fixedBase_ops] at hwfb
  rw [ulwc_append] at hwfb
  simp only [affAdd_localLength'] at hwfb
  rw [Circuit.foldlRange.usesLocalWitnesses] at hwfb
  have hwj := hwfb.2 i
  simp only [fixedBaseBody_localLength] at hwj
  simp only [← fbAcc_eq'] at hwj
  simp only [fixedBaseBody_eq, circuit_norm, ulwc_append] at hwj
  have hrow : Expression.eval env.toEnvironment
      (pm ((fbEb inp n).get ⟨2 * i.val, by omega⟩)
        ((fbEb inp n).get ⟨2 * i.val + 1, by omega⟩)
        - Expression.var (F := Fp) ⟨off6 inp n + 4 + i.val * 5⟩) = 0 := by
    have hc1 := muxConst4W_soundness_of_ulwc ((fbEb inp n).get ⟨2 * i.val, by omega⟩)
      ((fbEb inp n).get ⟨2 * i.val + 1, by omega⟩) (fixedTables.getD i.val #[]) env
      (off6 inp n + 4 + i.val * 5) hwj.1
    simp only [fixedTables_getD_row i.val i.isLt, muxConst4W, circuit_norm] at hc1
    simpa only [circuit_norm] using hc1
  exact fbWin_dx env.toEnvironment (fbEb inp n) (fbRb inp n) (fbSb inp n) Qpt Rpt H hH hgood
    (off6 inp n + 4) i.val i.isLt _ (hb ⟨2 * i.val, by omega⟩)
    (hb ⟨2 * i.val + 1, by omega⟩) hrow
    (fixedBase_fbInv_of_ulwc inp env n H hH Qpt Rpt hHX hHY hgood hw hb hdx0 i)

set_option linter.constructorNameAsVariable false in
/-- **The initial shift denominator of `main` does not vanish.** -/
theorem hfb0_of_ulwc (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (H : AffinePoint K) (hH : H.IsOnCurve params) (Qpt Rpt : Affine.Point Wp)
    (hHX : H.X = Expression.eval env.toEnvironment (seedPhase inp n).1.hx)
    (hgood : GoodOffset H hH (famOf env.toEnvironment (fbEb inp n) (fbRb inp n) (fbSb inp n)
      Qpt Rpt)) :
    Expression.eval env.toEnvironment (cst shiftX)
      - Expression.eval env.toEnvironment (seedPhase inp n).1.hx ≠ 0 := by
  have h := fbShift_dx env.toEnvironment (fbEb inp n) (fbRb inp n) (fbSb inp n) Qpt Rpt H hH hgood
  rw [hHX] at h
  simpa only [eval_cst] using h

end StandardECDSA.Phases
