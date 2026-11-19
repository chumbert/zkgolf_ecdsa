/-
# The shifted-table fields of `CompleteWitness` (gap G2)

`CompleteWitness` (`StandardECDSA/Main.lean`) carries six fields that are
statements about the *shifted-table* stage of `main`:

* `hshy` — the offset's `y`-coordinate does not vanish;
* `hs1`–`hs5` — the five distinct-`x` denominators of the stage.

All six are consequences of the stage's own rows plus a good offset.  The
denominators are *not* readable off the local witnesses alone (the `nonzero`
row is a constraint, not a witness definition), so the proof interleaves the
stage's row-level soundness with the bad-family avoidance:

```
hshy  --hshy_dx-->  affDouble sound  --affDouble_sound-->  2H  --hs1_dx-->  hs1
hs1   --affAdd sound-->  3H  --hs2_dx, hs3_dx-->  hs2, hs3
hs2,hs3 --affAdd sound-->  3H+Q  --hs4_dx-->  hs4
hs2,hs3 --affAdd sound-->  -3H+Q --hs5_dx-->  hs5
```

Each `hs*_dx` is a slot of the bad family, so the whole chain is driven by
`GoodOffset`; the only inputs are the stage's local witnesses and the
on-curve/nonsingularity facts for `H`, `Q`, `R`.

Gap G2 of `docs/m6-report.md`.
-/
import StandardECDSA.Witness.CompleteWitness
import StandardECDSA.Phases.HonestShifted
import StandardECDSA.Phases.HonestDenominators
import StandardECDSA.Phases.HonestWitness
import StandardECDSA.Phases.HonestFixedBase

namespace StandardECDSA

open WeierstrassCurve
open Circuit
open StandardECDSA.Gadgets
open StandardECDSA.Phases
open StandardECDSA.Math
open StandardECDSA.Witness

/-! ## The shifted-table stage's inputs -/

/-- The offset point `H` of `main`, as a pair of expressions. -/
abbrev shH (inp : Var Input Fp) (n : Nat) : Pt :=
  ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy)

/-- The public key `Q` of `main`, as a pair of expressions. -/
abbrev shQ (inp : Var Input Fp) : Pt := (inp.pkX, inp.pkY)

/-- The signature point `R` of `main`, as a pair of expressions. -/
abbrev shR (inp : Var Input Fp) (n : Nat) : Pt :=
  (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry)

/-! ## The honest shifted-table stage

The theorem below is the completeness-side counterpart of
`shiftedTables_soundness_of_ulwc`: it derives the stage's rows *and* its six
`CompleteWitness` denominators from the local witnesses plus a good offset. -/

set_option linter.constructorNameAsVariable false in
/-- **The shifted-table stage is honest.**  From the stage's local witnesses and
a good offset: the offset's `y`-coordinate is nonzero, the five distinct-`x`
denominators are nonzero, and the stage's rows hold. -/
theorem shiftedTables_honest (h q r : Pt) (env : ProverEnvironment Fp) (n : Nat)
    (hdeg : deg h.1 = 1)
    (eb rb sb : Vector E 256) (Qpt Rpt : Affine.Point Wp)
    (H : AffinePoint K) (hH : H.IsOnCurve params)
    (hHX : H.X = Expression.eval env h.1) (hHY : H.Y = Expression.eval env h.2)
    (hQns : NS (Expression.eval env q.1) (Expression.eval env q.2))
    (hQpt : Qpt = Affine.Point.some (Expression.eval env q.1) (Expression.eval env q.2) hQns)
    (hRns : NS (Expression.eval env r.1) (Expression.eval env r.2))
    (hRpt : Rpt = Affine.Point.some (Expression.eval env r.1) (Expression.eval env r.2) hRns)
    (hgood : GoodOffset H hH (famOf env eb rb sb Qpt Rpt))
    (hw : env.UsesLocalWitnessesCompleteness n ((shiftedTables h q r).operations n)) :
    (Expression.eval env h.2 ≠ 0) ∧
    (Expression.eval env h.1 - env.get (n + 2) ≠ 0) ∧
    (Expression.eval env q.1 - env.get (n + 6) ≠ 0) ∧
    (Expression.eval env r.1 - env.get (n + 6) ≠ 0) ∧
    (Expression.eval env r.1 - env.get (n + 10) ≠ 0) ∧
    (Expression.eval env r.1 - env.get (n + 22) ≠ 0) ∧
    ConstraintsHold.Soundness env ((shiftedTables h q r).operations n) := by
  classical
  have hHpt : goodOffsetAffinePt H hH = Affine.Point.some H.X H.Y (nsOfOnCurve H hH) :=
    goodOffsetAffinePt_eq_some H hH hgood
  -- the offset's `y`-coordinate
  have hshy : Expression.eval env h.2 ≠ 0 := by
    have hh := hshy_dx env eb rb sb Qpt Rpt H hH hgood
    rwa [hHY] at hh
  -- the stage's local witnesses, split into the eight sub-gadgets
  have hws := hw
  simp only [shiftedTables, circuit_norm] at hws
  simp only [affAdd_localLength', affDouble_localLength' hdeg, Nat.add_comm 4] at hws
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := hws
  -- `H` is nonsingular as an expression pair
  have hHns : NS (Expression.eval env h.1) (Expression.eval env h.2) :=
    ns_congr hHX.symm hHY.symm (nsOfOnCurve H hH)
  have h2y : 2 * Expression.eval env h.2 ≠ 0 :=
    mul_ne_zero (by decide) hshy
  -- ## step 1: `2H`
  have hd1 : ConstraintsHold.Soundness env ((affDouble h).operations n) :=
    affDouble_soundness_of_ulwc h env n w1 hshy
  obtain ⟨h2ns, h2eq⟩ := affDouble_sound env h n hdeg hHns h2y hd1
  have h2pt : Affine.Point.some (env.get (n + 2)) (env.get (n + 3)) h2ns
      = 2 • Affine.Point.some H.X H.Y (nsOfOnCurve H hH) := by
    rw [h2eq, some_congr hHX.symm hHY.symm hHns (nsOfOnCurve H hH)]
  have hs1 : Expression.eval env h.1 - env.get (n + 2) ≠ 0 := by
    have hh := hs1_dx env eb rb sb Qpt Rpt H hH hgood (env.get (n + 2)) (env.get (n + 3))
      h2ns (by rw [hHpt]; exact h2pt)
    rwa [hHX] at hh
  -- ## step 2: `3H`
  have hd2 : ConstraintsHold.Soundness env
      ((affAdd (affDouble h n).1 h).operations (n + 4)) :=
    affAdd_soundness_of_ulwc _ _ env _ w2 (by rw [affDouble_out_fst hdeg]; exact hs1)
  have h2ns' : NS (Expression.eval env (affDouble h n).1.1)
      (Expression.eval env (affDouble h n).1.2) :=
    ns_congr (affDouble_out_fst hdeg env n) (affDouble_out_snd hdeg env n) h2ns
  obtain ⟨h3ns, h3eq⟩ := affAdd_sound env (affDouble h n).1 h (n + 4) h2ns' hHns
    (by rw [affDouble_out_fst hdeg]; exact hs1) hd2
  have h3pt : Affine.Point.some (env.get (n + 6)) (env.get (n + 7)) h3ns
      = 3 • Affine.Point.some H.X H.Y (nsOfOnCurve H hH) := by
    rw [h3eq,
      some_congr (affDouble_out_fst hdeg env n) (affDouble_out_snd hdeg env n) h2ns' h2ns,
      some_congr hHX.symm hHY.symm hHns (nsOfOnCurve H hH), h2pt, nsmul_two_add]
  have hs2 : Expression.eval env q.1 - env.get (n + 6) ≠ 0 :=
    hs2_dx env eb rb sb Qpt Rpt H hH hgood (Expression.eval env q.1)
      (Expression.eval env q.2) hQns hQpt (env.get (n + 6)) (env.get (n + 7)) h3ns
      (by rw [hHpt]; exact h3pt)
  have hs3 : Expression.eval env r.1 - env.get (n + 6) ≠ 0 :=
    hs3_dx env eb rb sb Qpt Rpt H hH hgood (Expression.eval env r.1)
      (Expression.eval env r.2) hRns hRpt (env.get (n + 6)) (env.get (n + 7)) h3ns
      (by rw [hHpt]; exact h3pt)
  -- ## step 3: `3H + Q`
  have hd3 : ConstraintsHold.Soundness env
      ((affAdd (affAdd (affDouble h n).1 h (n + 4)).1 q).operations (n + 8)) :=
    affAdd_soundness_of_ulwc _ _ env _ w3
      (by rw [affAdd_out_fst (affDouble h n).1 h env (n + 4)]; exact hs2)
  have h3ns' : NS (Expression.eval env (affAdd (affDouble h n).1 h (n + 4)).1.1)
      (Expression.eval env (affAdd (affDouble h n).1 h (n + 4)).1.2) :=
    ns_congr (affAdd_out_fst (affDouble h n).1 h env (n + 4))
      (affAdd_out_snd (affDouble h n).1 h env (n + 4)) h3ns
  obtain ⟨h4ns, h4eq⟩ := affAdd_sound env (affAdd (affDouble h n).1 h (n + 4)).1 q (n + 8)
    h3ns' hQns (by rw [affAdd_out_fst (affDouble h n).1 h env (n + 4)]; exact hs2) hd3
  have h4pt : Affine.Point.some (env.get (n + 10)) (env.get (n + 11)) h4ns
      = 3 • Affine.Point.some H.X H.Y (nsOfOnCurve H hH) + Qpt := by
    rw [h4eq,
      some_congr (affAdd_out_fst (affDouble h n).1 h env (n + 4))
        (affAdd_out_snd (affDouble h n).1 h env (n + 4)) h3ns' h3ns, h3pt, hQpt]
  have hs4 : Expression.eval env r.1 - env.get (n + 10) ≠ 0 :=
    hs4_dx env eb rb sb Qpt Rpt H hH hgood (Expression.eval env r.1)
      (Expression.eval env r.2) hRns hRpt (env.get (n + 10)) (env.get (n + 11)) h4ns
      (by rw [hHpt]; exact h4pt)
  -- ## step 4: `-3H + Q`
  have hnegx : Expression.eval env (negPt (affAdd (affDouble h n).1 h (n + 4)).1).1
      = env.get (n + 6) := affAdd_out_fst (affDouble h n).1 h env (n + 4)
  have hnegy : Expression.eval env (negPt (affAdd (affDouble h n).1 h (n + 4)).1).2
      = -env.get (n + 7) := by
    simp only [negPt, eval_neg, affAdd_out_snd (affDouble h n).1 h env (n + 4)]
  have hd6 : ConstraintsHold.Soundness env
      ((affAdd (negPt (affAdd (affDouble h n).1 h (n + 4)).1) q).operations (n + 20)) :=
    affAdd_soundness_of_ulwc _ _ env _ w6 (by rw [hnegx]; exact hs2)
  have hnhns : NS (Expression.eval env (negPt (affAdd (affDouble h n).1 h (n + 4)).1).1)
      (Expression.eval env (negPt (affAdd (affDouble h n).1 h (n + 4)).1).2) :=
    ns_congr hnegx hnegy (negPt_ns h3ns)
  obtain ⟨h5ns, h5eq⟩ := affAdd_sound env
    (negPt (affAdd (affDouble h n).1 h (n + 4)).1) q (n + 20) hnhns hQns
    (by rw [hnegx]; exact hs2) hd6
  have h5pt : Affine.Point.some (env.get (n + 22)) (env.get (n + 23)) h5ns
      = -(3 • Affine.Point.some H.X H.Y (nsOfOnCurve H hH)) + Qpt := by
    rw [h5eq, some_congr hnegx hnegy hnhns (negPt_ns h3ns),
      negPt_group (env.get (n + 6)) (env.get (n + 7)) h3ns, h3pt, hQpt]
  have hs5 : Expression.eval env r.1 - env.get (n + 22) ≠ 0 :=
    hs5_dx env eb rb sb Qpt Rpt H hH hgood (Expression.eval env r.1)
      (Expression.eval env r.2) hRns hRpt (env.get (n + 22)) (env.get (n + 23)) h5ns
      (by rw [hHpt]; exact h5pt)
  -- ## assemble
  refine ⟨hshy, hs1, hs2, hs3, hs4, hs5, ?_⟩
  exact shiftedTables_soundness_of_ulwc h q r env n hw hdeg hshy hs1 hs2 hs3 hs4 hs5

/-! ## Extracting the shifted-table stage of `main` -/

/-- The shifted-table stage's local witnesses, extracted from `main`'s. -/
theorem main_ulwc_shiftedTables (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (h : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    env.UsesLocalWitnessesCompleteness (off7 inp n)
      ((shiftedTables (shH inp n) (shQ inp) (shR inp n) (off7 inp n)).2) := by
  rw [main_ops'] at h
  simp only [List.append_assoc] at h
  obtain ⟨-, h⟩ := ulwc_append_left h
  obtain ⟨-, h⟩ := ulwc_append_left h
  obtain ⟨-, h⟩ := ulwc_append_left h
  obtain ⟨-, h⟩ := ulwc_append_left h
  obtain ⟨-, h⟩ := ulwc_append_left h
  obtain ⟨-, h⟩ := ulwc_append_left h
  obtain ⟨-, h⟩ := ulwc_append_left h
  obtain ⟨h8, -⟩ := ulwc_append_left h
  exact h8

/-! ## Nonsingularity from the curve equation -/

/-- The curve equation gives nonsingularity of the affine point. -/
theorem ns_of_curve_eq (H : AffinePoint K)
    (h : H.Y ^ 2 = H.X ^ 3 + pa * H.X + pb) : NS H.X H.Y := by
  refine Affine.equation_iff_nonsingular.mp ?_
  rw [Affine.equation_iff]
  dsimp [Wp, AffineBridge.W, CurveParameters.toMathlib]
  rw [show params.a = pa from rfl, show params.b = pb from rfl]
  linear_combination h

/-! ## The shifted-table stage of `main` -/

set_option linter.constructorNameAsVariable false in
/-- **The shifted-table stage of `main` is honest.** -/
theorem shiftedTables_honest_of_main (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (H : AffinePoint K) (hH : H.IsOnCurve params) (Qpt Rpt : Affine.Point Wp)
    (hHX : H.X = Expression.eval env (seedPhase inp n).1.hx)
    (hHY : H.Y = Expression.eval env (seedPhase inp n).1.hy)
    (hQns : NS (Expression.eval env inp.pkX) (Expression.eval env inp.pkY))
    (hQpt : Qpt = Affine.Point.some (Expression.eval env inp.pkX)
      (Expression.eval env inp.pkY) hQns)
    (hRns : NS (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow))
      (Expression.eval env (seedPhase inp n).1.ry))
    (hRpt : Rpt = Affine.Point.some
      (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow))
      (Expression.eval env (seedPhase inp n).1.ry) hRns)
    (hgood : GoodOffset H hH (famOf env (fbEb inp n) (fbRb inp n) (fbSb inp n) Qpt Rpt))
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    (Expression.eval env (seedPhase inp n).1.hy ≠ 0) ∧
    (Expression.eval env (seedPhase inp n).1.hx - env.get (off7 inp n + 2) ≠ 0) ∧
    (Expression.eval env inp.pkX - env.get (off7 inp n + 6) ≠ 0) ∧
    (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow)
      - env.get (off7 inp n + 6) ≠ 0) ∧
    (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow)
      - env.get (off7 inp n + 10) ≠ 0) ∧
    (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow)
      - env.get (off7 inp n + 22) ≠ 0) ∧
    ConstraintsHold.Soundness env
      ((shiftedTables (shH inp n) (shQ inp) (shR inp n)).operations (off7 inp n)) :=
  shiftedTables_honest (shH inp n) (shQ inp) (shR inp n) env (off7 inp n)
    (seed_hx_deg inp n) (fbEb inp n) (fbRb inp n) (fbSb inp n) Qpt Rpt H hH hHX hHY
    hQns hQpt hRns hRpt hgood (main_ulwc_shiftedTables inp env n hw)

/-- `CompleteWitness.hshy`. -/
theorem hshy_of_ulwc (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (H : AffinePoint K) (hH : H.IsOnCurve params) (Qpt Rpt : Affine.Point Wp)
    (hHX : H.X = Expression.eval env (seedPhase inp n).1.hx)
    (hHY : H.Y = Expression.eval env (seedPhase inp n).1.hy)
    (hQns : NS (Expression.eval env inp.pkX) (Expression.eval env inp.pkY))
    (hQpt : Qpt = Affine.Point.some (Expression.eval env inp.pkX)
      (Expression.eval env inp.pkY) hQns)
    (hRns : NS (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow))
      (Expression.eval env (seedPhase inp n).1.ry))
    (hRpt : Rpt = Affine.Point.some
      (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow))
      (Expression.eval env (seedPhase inp n).1.ry) hRns)
    (hgood : GoodOffset H hH (famOf env (fbEb inp n) (fbRb inp n) (fbSb inp n) Qpt Rpt))
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    Expression.eval env (seedPhase inp n).1.hy ≠ 0 :=
  (shiftedTables_honest_of_main inp env n H hH Qpt Rpt hHX hHY hQns hQpt hRns hRpt hgood hw).1

/-- `CompleteWitness.hs1`. -/
theorem hs1_of_ulwc (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (H : AffinePoint K) (hH : H.IsOnCurve params) (Qpt Rpt : Affine.Point Wp)
    (hHX : H.X = Expression.eval env (seedPhase inp n).1.hx)
    (hHY : H.Y = Expression.eval env (seedPhase inp n).1.hy)
    (hQns : NS (Expression.eval env inp.pkX) (Expression.eval env inp.pkY))
    (hQpt : Qpt = Affine.Point.some (Expression.eval env inp.pkX)
      (Expression.eval env inp.pkY) hQns)
    (hRns : NS (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow))
      (Expression.eval env (seedPhase inp n).1.ry))
    (hRpt : Rpt = Affine.Point.some
      (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow))
      (Expression.eval env (seedPhase inp n).1.ry) hRns)
    (hgood : GoodOffset H hH (famOf env (fbEb inp n) (fbRb inp n) (fbSb inp n) Qpt Rpt))
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    Expression.eval env (seedPhase inp n).1.hx - env.get (off7 inp n + 2) ≠ 0 :=
  (shiftedTables_honest_of_main inp env n H hH Qpt Rpt hHX hHY hQns hQpt hRns hRpt hgood hw).2.1

/-- `CompleteWitness.hs2`. -/
theorem hs2_of_ulwc (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (H : AffinePoint K) (hH : H.IsOnCurve params) (Qpt Rpt : Affine.Point Wp)
    (hHX : H.X = Expression.eval env (seedPhase inp n).1.hx)
    (hHY : H.Y = Expression.eval env (seedPhase inp n).1.hy)
    (hQns : NS (Expression.eval env inp.pkX) (Expression.eval env inp.pkY))
    (hQpt : Qpt = Affine.Point.some (Expression.eval env inp.pkX)
      (Expression.eval env inp.pkY) hQns)
    (hRns : NS (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow))
      (Expression.eval env (seedPhase inp n).1.ry))
    (hRpt : Rpt = Affine.Point.some
      (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow))
      (Expression.eval env (seedPhase inp n).1.ry) hRns)
    (hgood : GoodOffset H hH (famOf env (fbEb inp n) (fbRb inp n) (fbSb inp n) Qpt Rpt))
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    Expression.eval env inp.pkX - env.get (off7 inp n + 6) ≠ 0 :=
  (shiftedTables_honest_of_main inp env n H hH Qpt Rpt hHX hHY hQns hQpt hRns hRpt hgood hw).2.2.1

/-- `CompleteWitness.hs3`. -/
theorem hs3_of_ulwc (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (H : AffinePoint K) (hH : H.IsOnCurve params) (Qpt Rpt : Affine.Point Wp)
    (hHX : H.X = Expression.eval env (seedPhase inp n).1.hx)
    (hHY : H.Y = Expression.eval env (seedPhase inp n).1.hy)
    (hQns : NS (Expression.eval env inp.pkX) (Expression.eval env inp.pkY))
    (hQpt : Qpt = Affine.Point.some (Expression.eval env inp.pkX)
      (Expression.eval env inp.pkY) hQns)
    (hRns : NS (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow))
      (Expression.eval env (seedPhase inp n).1.ry))
    (hRpt : Rpt = Affine.Point.some
      (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow))
      (Expression.eval env (seedPhase inp n).1.ry) hRns)
    (hgood : GoodOffset H hH (famOf env (fbEb inp n) (fbRb inp n) (fbSb inp n) Qpt Rpt))
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow)
      - env.get (off7 inp n + 6) ≠ 0 :=
  (shiftedTables_honest_of_main inp env n H hH Qpt Rpt hHX hHY hQns hQpt hRns hRpt hgood hw).2.2.2.1

/-- `CompleteWitness.hs4`. -/
theorem hs4_of_ulwc (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (H : AffinePoint K) (hH : H.IsOnCurve params) (Qpt Rpt : Affine.Point Wp)
    (hHX : H.X = Expression.eval env (seedPhase inp n).1.hx)
    (hHY : H.Y = Expression.eval env (seedPhase inp n).1.hy)
    (hQns : NS (Expression.eval env inp.pkX) (Expression.eval env inp.pkY))
    (hQpt : Qpt = Affine.Point.some (Expression.eval env inp.pkX)
      (Expression.eval env inp.pkY) hQns)
    (hRns : NS (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow))
      (Expression.eval env (seedPhase inp n).1.ry))
    (hRpt : Rpt = Affine.Point.some
      (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow))
      (Expression.eval env (seedPhase inp n).1.ry) hRns)
    (hgood : GoodOffset H hH (famOf env (fbEb inp n) (fbRb inp n) (fbSb inp n) Qpt Rpt))
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow)
      - env.get (off7 inp n + 10) ≠ 0 :=
  (shiftedTables_honest_of_main inp env n H hH Qpt Rpt hHX hHY hQns hQpt hRns hRpt hgood hw).2.2.2.2.1

/-- `CompleteWitness.hs5`. -/
theorem hs5_of_ulwc (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (H : AffinePoint K) (hH : H.IsOnCurve params) (Qpt Rpt : Affine.Point Wp)
    (hHX : H.X = Expression.eval env (seedPhase inp n).1.hx)
    (hHY : H.Y = Expression.eval env (seedPhase inp n).1.hy)
    (hQns : NS (Expression.eval env inp.pkX) (Expression.eval env inp.pkY))
    (hQpt : Qpt = Affine.Point.some (Expression.eval env inp.pkX)
      (Expression.eval env inp.pkY) hQns)
    (hRns : NS (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow))
      (Expression.eval env (seedPhase inp n).1.ry))
    (hRpt : Rpt = Affine.Point.some
      (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow))
      (Expression.eval env (seedPhase inp n).1.ry) hRns)
    (hgood : GoodOffset H hH (famOf env (fbEb inp n) (fbRb inp n) (fbSb inp n) Qpt Rpt))
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow)
      - env.get (off7 inp n + 22) ≠ 0 :=
  (shiftedTables_honest_of_main inp env n H hH Qpt Rpt hHX hHY hQns hQpt hRns hRpt hgood hw).2.2.2.2.2.1

/-- The shifted-table stage's rows hold for `main`'s honest witness. -/
theorem shiftedTables_soundness_of_main (inp : Var Input Fp) (env : ProverEnvironment Fp)
    (n : Nat) (H : AffinePoint K) (hH : H.IsOnCurve params) (Qpt Rpt : Affine.Point Wp)
    (hHX : H.X = Expression.eval env (seedPhase inp n).1.hx)
    (hHY : H.Y = Expression.eval env (seedPhase inp n).1.hy)
    (hQns : NS (Expression.eval env inp.pkX) (Expression.eval env inp.pkY))
    (hQpt : Qpt = Affine.Point.some (Expression.eval env inp.pkX)
      (Expression.eval env inp.pkY) hQns)
    (hRns : NS (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow))
      (Expression.eval env (seedPhase inp n).1.ry))
    (hRpt : Rpt = Affine.Point.some
      (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow))
      (Expression.eval env (seedPhase inp n).1.ry) hRns)
    (hgood : GoodOffset H hH (famOf env (fbEb inp n) (fbRb inp n) (fbSb inp n) Qpt Rpt))
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    ConstraintsHold.Soundness env
      ((shiftedTables (shH inp n) (shQ inp) (shR inp n)).operations (off7 inp n)) :=
  (shiftedTables_honest_of_main inp env n H hH Qpt Rpt hHX hHY hQns hQpt hRns hRpt hgood hw).2.2.2.2.2.2

/-- The shifted-table stage's table-point spec for `main`'s honest witness. -/
theorem shiftedTables_htab_of_main (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (H : AffinePoint K) (hH : H.IsOnCurve params) (Qpt Rpt : Affine.Point Wp)
    (hHX : H.X = Expression.eval env (seedPhase inp n).1.hx)
    (hHY : H.Y = Expression.eval env (seedPhase inp n).1.hy)
    (hQns : NS (Expression.eval env inp.pkX) (Expression.eval env inp.pkY))
    (hQpt : Qpt = Affine.Point.some (Expression.eval env inp.pkX)
      (Expression.eval env inp.pkY) hQns)
    (hRns : NS (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow))
      (Expression.eval env (seedPhase inp n).1.ry))
    (hRpt : Rpt = Affine.Point.some
      (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow))
      (Expression.eval env (seedPhase inp n).1.ry) hRns)
    (hgood : GoodOffset H hH (famOf env (fbEb inp n) (fbRb inp n) (fbSb inp n) Qpt Rpt))
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    ∀ (j : Nat) (hj : j < 256) (v w : Fp), (v = 0 ∨ v = 1) → (w = 0 ∨ w = 1) →
      ∃ hns : NS (if v = 0 then
            (if w = 0 then Expression.eval env
                (((shiftedTables (shH inp n) (shQ inp) (shR inp n) (off7 inp n)).1.x0 j).1)
              else Expression.eval env
                (((shiftedTables (shH inp n) (shQ inp) (shR inp n) (off7 inp n)).1.x2 j).1))
          else (if w = 0 then Expression.eval env
              (((shiftedTables (shH inp n) (shQ inp) (shR inp n) (off7 inp n)).1.x1 j).1)
            else Expression.eval env
              (((shiftedTables (shH inp n) (shQ inp) (shR inp n) (off7 inp n)).1.x3 j).1)))
          (if v = 0 then
            (if w = 0 then Expression.eval env
                (((shiftedTables (shH inp n) (shQ inp) (shR inp n) (off7 inp n)).1.x0 j).2)
              else Expression.eval env
                (((shiftedTables (shH inp n) (shQ inp) (shR inp n) (off7 inp n)).1.x2 j).2))
          else (if w = 0 then Expression.eval env
              (((shiftedTables (shH inp n) (shQ inp) (shR inp n) (off7 inp n)).1.x1 j).2)
            else Expression.eval env
              (((shiftedTables (shH inp n) (shQ inp) (shR inp n) (off7 inp n)).1.x3 j).2))),
        Affine.Point.some _ _ hns
          = (3 * sigma j) • goodOffsetAffinePt H hH
            + (if v = 1 then (1 : ℤ) else 0) • Qpt
            + (if w = 1 then (1 : ℤ) else 0) • Rpt := by
  classical
  have hHpt : goodOffsetAffinePt H hH = Affine.Point.some H.X H.Y (nsOfOnCurve H hH) :=
    goodOffsetAffinePt_eq_some H hH hgood
  have hHns : NS (Expression.eval env (shH inp n).1) (Expression.eval env (shH inp n).2) :=
    ns_congr hHX.symm hHY.symm (nsOfOnCurve H hH)
  obtain ⟨hy, hs1, hs2, hs3, hs4, hs5, hc⟩ :=
    shiftedTables_honest_of_main inp env n H hH Qpt Rpt hHX hHY hQns hQpt hRns hRpt hgood hw
  intro j hj v w hv hwv
  obtain ⟨hns, heq⟩ := shiftedTables_htab env (shH inp n) (shQ inp) (shR inp n) (off7 inp n)
    (seed_hx_deg inp n) hHns hQns hRns (mul_ne_zero (by decide) hy)
    hs1 hs2 hs3 hs4 hs5 hc j hj v w hv hwv
  refine ⟨hns, ?_⟩
  rw [heq, hHpt, some_congr hHX.symm hHY.symm hHns (nsOfOnCurve H hH), hQpt, hRpt]

end StandardECDSA
