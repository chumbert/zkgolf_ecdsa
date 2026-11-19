/-
# The hint-derived fields of `CompleteWitness` (gap G2, step 3, partial)

`CompleteWitness` (`StandardECDSA/Main.lean`) is the bundle of witness facts the
honest prover must supply for `main_complete_with_seed`.  Its 29 fields split into
two groups:

**Hint-derived (this module).**  The four Boolean-ness fields `hov`, `hb`, `hb'`,
`hb''` are statements about the *wires* the seed and bits stages allocate.  By
`StandardECDSA.Witness.main_hint_cells` those wires are exactly the 772 cells of
the seed, so these fields follow from `ScalarFacts` alone — no group theory, no
constraint reasoning.

**Still open (documented below).**  The remaining 25 fields need

* the *input embedding* (`Expression.eval env inp.pkX = pkX`, …) for `hQ`, `hR`,
  `hH`, `hr`, `ht`, `hd0`–`hd3`, `hle`, `hle'`, `hleg`;
* the honest-witness group invariants `fbInv` (128 fixed-base windows) and
  `ladInv` (255 ladder steps) for `hfb0`, `hfb`, `hshy`, `hs1`–`hs5`, `hj1`,
  `hj2`, `hjf1`–`hjf4` — the inductions `fbStep` + `fin_foldl_inv` +
  `foldlAcc_eq` and `ladInv` + `ladAccH_eq` + `Tpt`, whose *per-step* bricks
  (`fbWin_dx`, `fbShift_dx`, `hshy_dx`, `hs1_dx`–`hs5_dx`, `hj1_dx`, `hj2_dx`,
  `hjf1_dx`, `hjf2_dx`, `jointLadder_denominators`) are already proved in
  `StandardECDSA/Phases/HonestDenominators.lean`,
  `StandardECDSA/Phases/HonestShifted.lean` and
  `StandardECDSA/Phases/LadderSemantics.lean`.

Gap G2 of `docs/m6-report.md`.
-/
import StandardECDSA.Main
import StandardECDSA.Witness.Hint
import StandardECDSA.Witness.HintBridge
import StandardECDSA.Witness.Seed

namespace StandardECDSA

open Circuit
open StandardECDSA.Gadgets
open StandardECDSA.Phases
open StandardECDSA.Math
open StandardECDSA.Witness

/-! ## The seed stage's output expressions -/

/-- The seed stage's `overflow` expression evaluates to the seed's overflow cell. -/
theorem eval_seedPhase_overflow (inp : Var Input Fp) (s : Witness.Seed)
    (env : ProverEnvironment Fp) (n : Nat) (hhint : env.hint = seedHint s)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    Expression.eval env (seedPhase inp n).1.overflow = s.overflow := by
  rw [seedPhase_out_overflow, eval_var]
  exact ((main_hint_cells inp s env n hhint hw).2.2.2.1).trans (seedCells_getD_ov s)

/-- The seed stage's `ry` expression evaluates to the seed's `ry` cell. -/
theorem eval_seedPhase_ry (inp : Var Input Fp) (s : Witness.Seed)
    (env : ProverEnvironment Fp) (n : Nat) (hhint : env.hint = seedHint s)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    Expression.eval env (seedPhase inp n).1.ry = s.ry := by
  rw [seedPhase_out_ry, eval_var]
  exact ((main_hint_cells inp s env n hhint hw).1).trans (seedCells_getD_ry s)

/-- The seed stage's `hx` expression evaluates to the seed's `hx` cell. -/
theorem eval_seedPhase_hx (inp : Var Input Fp) (s : Witness.Seed)
    (env : ProverEnvironment Fp) (n : Nat) (hhint : env.hint = seedHint s)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    Expression.eval env (seedPhase inp n).1.hx = s.hx := by
  rw [seedPhase_out_hx, eval_var]
  exact ((main_hint_cells inp s env n hhint hw).2.1).trans (seedCells_getD_hx s)

/-- The seed stage's `hy` expression evaluates to the seed's `hy` cell. -/
theorem eval_seedPhase_hy (inp : Var Input Fp) (s : Witness.Seed)
    (env : ProverEnvironment Fp) (n : Nat) (hhint : env.hint = seedHint s)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    Expression.eval env (seedPhase inp n).1.hy = s.hy := by
  rw [seedPhase_out_hy, eval_var]
  exact ((main_hint_cells inp s env n hhint hw).2.2.1).trans (seedCells_getD_hy s)

/-! ## The bits stage's output expressions -/

theorem bitsPhase_out_eb (n : Nat) (k : Fin 256) :
    (bitsPhase n).1.eb.get k = Expression.var (F := Fp) ⟨n + k.val⟩ := by
  show ((bitsPhase).output n).eb.get k = _
  rw [bitsPhase_out]
  exact bitVec_out 4 3 n k

theorem bitsPhase_out_rb (n : Nat) (k : Fin 256) :
    (bitsPhase n).1.rb.get k = Expression.var (F := Fp) ⟨n + 256 + k.val⟩ := by
  show ((bitsPhase).output n).rb.get k = _
  rw [bitsPhase_out]
  exact bitVec_out 5 3 (n + 256) k

theorem bitsPhase_out_sb (n : Nat) (k : Fin 256) :
    (bitsPhase n).1.sb.get k = Expression.var (F := Fp) ⟨n + 512 + k.val⟩ := by
  show ((bitsPhase).output n).sb.get k = _
  rw [bitsPhase_out]
  exact bitVec_out 6 3 (n + 512) k

/-! ## The four hint-derived `CompleteWitness` fields -/

/-- `CompleteWitness.hov`: the overflow wire is Boolean. -/
theorem hov_of_ulwc (inp : Var Input Fp) (s : Witness.Seed) (env : ProverEnvironment Fp)
    (n : Nat) (E r t : Nat) (hhint : env.hint = seedHint s)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hsc : ScalarFacts s E r t) :
    Expression.eval env (seedPhase inp n).1.overflow = 0 ∨
      Expression.eval env (seedPhase inp n).1.overflow = 1 := by
  rw [eval_seedPhase_overflow inp s env n hhint hw]
  exact hsc.overflow_bool

/-- `CompleteWitness.hb`: the digest-bit wires are Boolean. -/
theorem hb_of_ulwc (inp : Var Input Fp) (s : Witness.Seed) (env : ProverEnvironment Fp)
    (n : Nat) (E r t : Nat) (hhint : env.hint = seedHint s)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hsc : ScalarFacts s E r t) :
    ∀ k : Fin 256,
      Expression.eval env.toEnvironment ((bitsPhase (off3 inp n)).1.eb.get k) = 0 ∨
        Expression.eval env.toEnvironment ((bitsPhase (off3 inp n)).1.eb.get k) = 1 := by
  intro k
  rw [bitsPhase_out_eb, eval_var]
  rw [((main_hint_cells inp s env n hhint hw).2.2.2.2.1 k), seedCells_getD_digest]
  exact hsc.digestBits_bool k

/-- `CompleteWitness.hb'`: the `r`-bit wires are Boolean. -/
theorem hbR_of_ulwc (inp : Var Input Fp) (s : Witness.Seed) (env : ProverEnvironment Fp)
    (n : Nat) (E r t : Nat) (hhint : env.hint = seedHint s)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hsc : ScalarFacts s E r t) :
    ∀ k : Fin 256,
      Expression.eval env.toEnvironment ((bitsPhase (off3 inp n)).1.rb.get k) = 0 ∨
        Expression.eval env.toEnvironment ((bitsPhase (off3 inp n)).1.rb.get k) = 1 := by
  intro k
  rw [bitsPhase_out_rb, eval_var]
  rw [((main_hint_cells inp s env n hhint hw).2.2.2.2.2.1 k), seedCells_getD_r]
  exact hsc.rBits_bool k

/-- `CompleteWitness.hb''`: the `t`-bit wires are Boolean. -/
theorem hbT_of_ulwc (inp : Var Input Fp) (s : Witness.Seed) (env : ProverEnvironment Fp)
    (n : Nat) (E r t : Nat) (hhint : env.hint = seedHint s)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hsc : ScalarFacts s E r t) :
    ∀ k : Fin 256,
      Expression.eval env.toEnvironment ((bitsPhase (off3 inp n)).1.sb.get k) = 0 ∨
        Expression.eval env.toEnvironment ((bitsPhase (off3 inp n)).1.sb.get k) = 1 := by
  intro k
  rw [bitsPhase_out_sb, eval_var]
  rw [((main_hint_cells inp s env n hhint hw).2.2.2.2.2.2 k), seedCells_getD_t]
  exact hsc.tBits_bool k

end StandardECDSA
