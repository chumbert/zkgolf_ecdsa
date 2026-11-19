/-
# Honest-witness denominators (task G2-b, ladder part) — infrastructure

`CompleteWitness` (`StandardECDSA/Main.lean`) carries the ladder denominators
`hshy`, `hs1..hs5`, `hj1`, `hj2`, `hjf1..hjf4` as explicit hypotheses.  This
module supplies the *row-level* soundness lemmas the ladder induction needs,
mirroring the completeness lemmas of `Main.lean`:

* `elmTo_soundness_of_ulwc` — the `elmTo` gadget's six rows from local witnesses;
* `jointLadderFinal_soundness_of_ulwc` — the ladder's final step.

Every proof is complete; no new axioms and no `native_decide`.
-/

import StandardECDSA.Phases.HonestFixedBase
import StandardECDSA.HonestLadder

namespace StandardECDSA.Phases

open WeierstrassCurve StandardECDSA StandardECDSA.Gadgets StandardECDSA.Math
open StandardECDSA.Math.FixedTables

/-! ## `elmTo` -/

/-- The `elmTo` gadget's rows hold for the honest witness. -/
theorem elmTo_soundness_of_ulwc (p q target : Pt) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((elmTo p q target).operations n))
    (hDx : Expression.eval env.toEnvironment q.1 - Expression.eval env.toEnvironment p.1 ≠ 0)
    (hDx2 : Expression.eval env.toEnvironment p.1 - env.get (n + 2) ≠ 0)
    (h1 : env.get (n + 3) * env.get (n + 3) - Expression.eval env.toEnvironment p.1
      - env.get (n + 2) - Expression.eval env.toEnvironment target.1 = 0)
    (h2 : env.get (n + 3) * (Expression.eval env.toEnvironment p.1
      - Expression.eval env.toEnvironment target.1) - Expression.eval env.toEnvironment p.2
      - Expression.eval env.toEnvironment target.2 = 0) :
    ConstraintsHold.Soundness env ((elmTo p q target).operations n) := by
  simp only [elmTo, elmCore, nonzero, circuit_norm, pm] at hw ⊢
  obtain ⟨e1, e2, e3, e4⟩ := hw
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]; simp only [eval_cst]; linear_combination mul_inv_cancel₀ hDx
  · rw [e2, e1]; field_simp; ring
  · rw [e3]; ring
  · rw [e4]; field_simp; ring
  · exact h1
  · exact h2

/-! ## The ladder's final step -/

/-- The ladder's final step's rows hold for the honest witness. -/
theorem jointLadderFinal_soundness_of_ulwc (tables : Tables) (rb sb : Vector E 256)
    (acc target : Pt) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n
      ((jointLadderFinal tables rb sb acc target).operations n))
    (hDx : Expression.eval env.toEnvironment
        ((mux4W (rb.get ⟨0, by omega⟩) (sb.get ⟨0, by omega⟩)
          (tables.x0 255) (tables.x1 255) (tables.x2 255) (tables.x3 255)).output n).1
      - Expression.eval env.toEnvironment acc.1 ≠ 0)
    (hDx2 : Expression.eval env.toEnvironment acc.1 - env.get (n + 6 + 2) ≠ 0)
    (h1 : env.get (n + 6 + 3) * env.get (n + 6 + 3) - Expression.eval env.toEnvironment acc.1
      - env.get (n + 6 + 2) - Expression.eval env.toEnvironment target.1 = 0)
    (h2 : env.get (n + 6 + 3) * (Expression.eval env.toEnvironment acc.1
      - Expression.eval env.toEnvironment target.1) - Expression.eval env.toEnvironment acc.2
      - Expression.eval env.toEnvironment target.2 = 0) :
    ConstraintsHold.Soundness env ((jointLadderFinal tables rb sb acc target).operations n) := by
  rw [jointLadderFinal_ops] at hw ⊢
  simp only [ConstraintsHold.Soundness, Operations.forAllNoOffset_append]
  rw [ulwc_append] at hw
  simp only [mux4W_localLength] at hw
  refine ⟨mux4W_soundness_of_ulwc _ _ _ _ _ _ env n hw.1, ?_⟩
  exact elmTo_soundness_of_ulwc acc _ target env (n + 6) hw.2 hDx hDx2 h1 h2

/-! ## The whole ladder phase -/

/-- The joint-ladder phase's rows hold for the honest witness. -/
theorem jointLadder_soundness_of_ulwc (acc0 : Pt) (tables : Tables) (rb sb : Vector E 256)
    (target : Pt) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n
      ((jointLadder acc0 tables rb sb target).operations n))
    (hDx : ∀ i : Fin 255, Expression.eval env.toEnvironment
        ((mux4W (rb.get ⟨255 - i.val, by omega⟩) (sb.get ⟨255 - i.val, by omega⟩)
          (tables.x0 i.val) (tables.x1 i.val) (tables.x2 i.val)
          (tables.x3 i.val)).output (n + i.val * 12)).1
      - Expression.eval env.toEnvironment (jlAcc acc0 tables rb sb n i).1 ≠ 0)
    (hDx2 : ∀ i : Fin 255, Expression.eval env.toEnvironment (jlAcc acc0 tables rb sb n i).1
      - env.get (n + i.val * 12 + 6 + 2) ≠ 0)
    (hDxf : Expression.eval env.toEnvironment
        ((mux4W (rb.get ⟨0, by omega⟩) (sb.get ⟨0, by omega⟩)
          (tables.x0 255) (tables.x1 255) (tables.x2 255) (tables.x3 255)).output
          (n + 3060)).1
      - Expression.eval env.toEnvironment (jlOut acc0 tables rb sb n).1 ≠ 0)
    (hDx2f : Expression.eval env.toEnvironment (jlOut acc0 tables rb sb n).1
      - env.get (n + 3060 + 6 + 2) ≠ 0)
    (h1f : env.get (n + 3060 + 6 + 3) * env.get (n + 3060 + 6 + 3)
      - Expression.eval env.toEnvironment (jlOut acc0 tables rb sb n).1
      - env.get (n + 3060 + 6 + 2) - Expression.eval env.toEnvironment target.1 = 0)
    (h2f : env.get (n + 3060 + 6 + 3) * (Expression.eval env.toEnvironment
        (jlOut acc0 tables rb sb n).1 - Expression.eval env.toEnvironment target.1)
      - Expression.eval env.toEnvironment (jlOut acc0 tables rb sb n).2
      - Expression.eval env.toEnvironment target.2 = 0) :
    ConstraintsHold.Soundness env ((jointLadder acc0 tables rb sb target).operations n) := by
  rw [jointLadder_ops] at hw ⊢
  simp only [ConstraintsHold.Soundness, Operations.forAllNoOffset_append]
  rw [ulwc_append] at hw
  simp only [jointLadderFold_localLength] at hw
  refine ⟨?_, ?_⟩
  · rw [Circuit.foldlRange.forAllNoOffset]
    rw [Circuit.foldlRange.usesLocalWitnesses] at hw
    intro i
    simp only [jointLadderBody_localLength] at hw ⊢
    simp only [← jlAcc_eq] at hw ⊢
    have hwi := hw.1 i
    rw [jointLadderBody_ops, ulwc_append] at hwi
    simp only [mux4W_localLength] at hwi
    exact jointLadderBody_soundness_of_ulwc tables rb sb (jlAcc acc0 tables rb sb n i) i env
      (n + i.val * 12) hwi.1 hwi.2 (hDx i) (hDx2 i)
  · rw [jlOut_eq] at hDxf hDx2f h1f h2f
    exact jointLadderFinal_soundness_of_ulwc tables rb sb _ target env (n + 3060) hw.2
      hDxf hDx2f h1f h2f

end StandardECDSA.Phases
