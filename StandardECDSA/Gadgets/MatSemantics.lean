/-
# Semantic soundness of the `mat` lowering

`mat e` allocates one wire per non-constant product of `e` and constrains each
wire to the corresponding product.  This file proves the semantic statement that
the rest of the gadget soundness proofs consume: **any** assignment satisfying
the rows of `mat e` makes the output expression evaluate to the value of `e`.

The statement is phrased for an arbitrary `ConditionNoOffset` whose `assert`
component implies vanishing, so it applies both to `ConstraintsHold` and to the
`ConstraintsHold.Soundness` condition produced by `circuit_proof_start`.

Task T05 (semantic half).
-/

import StandardECDSA.Gadgets.MatExplicit

namespace StandardECDSA.Gadgets

theorem mat_eval_gen (e : E) : ∀ n (env : Environment Fp) (c : ConditionNoOffset Fp),
    (∀ x, c.assert x → Expression.eval env x = 0) →
    Operations.forAllNoOffset c ((mat e) n).2 →
    Expression.eval env (matOut e n) = Expression.eval env e := by
  induction e with
  | var v =>
      intro n env c _ _
      rfl
  | const k =>
      intro n env c _ _
      rfl
  | add a b iha ihb =>
      intro n env c hc h
      rw [mat_operations_eq] at h
      rw [matOps, Operations.forAllNoOffset_append] at h
      have h1 : Operations.forAllNoOffset c ((mat a) n).2 := by
        rw [mat_operations_eq]; exact h.1
      have h2 : Operations.forAllNoOffset c ((mat b) (n + matLen a)).2 := by
        rw [mat_operations_eq]; exact h.2
      rw [matOut]
      simp only [circuit_norm, iha n env c hc h1, ihb _ env c hc h2]
  | mul a b iha ihb =>
      intro n env c hc h
      rw [mat_operations_eq] at h
      rw [matOps, Operations.forAllNoOffset_append] at h
      obtain ⟨h1, h2⟩ := h
      have h1' : Operations.forAllNoOffset c ((mat a) n).2 := by
        rw [mat_operations_eq]; exact h1
      by_cases hb : deg a = 0 ∨ deg b = 0
      · rw [if_pos hb] at h2
        rw [Operations.forAllNoOffset_append] at h2
        have h2' : Operations.forAllNoOffset c ((mat b) (n + matLen a)).2 := by
          rw [mat_operations_eq]; exact h2.1
        rw [matOut, if_pos hb]
        simp only [circuit_norm, iha n env c hc h1', ihb _ env c hc h2']
      · rw [if_neg hb] at h2
        rw [Operations.forAllNoOffset_append] at h2
        obtain ⟨h2a, h2b⟩ := h2
        have h2a' : Operations.forAllNoOffset c ((mat b) (n + matLen a)).2 := by
          rw [mat_operations_eq]; exact h2a
        have h2c : Expression.eval env
            (matOut a n * matOut b (n + matLen a) - var ⟨n + matLen a + matLen b⟩) = 0 :=
          hc _ h2b.2.1
        have hrow : Expression.eval env (matOut a n) * Expression.eval env (matOut b (n + matLen a))
            - env.get (n + matLen a + matLen b) = 0 := by
          simpa only [circuit_norm] using h2c
        have hval : env.get (n + matLen a + matLen b)
            = Expression.eval env (matOut a n) * Expression.eval env (matOut b (n + matLen a)) :=
          (sub_eq_zero.mp hrow).symm
        rw [matOut, if_neg hb]
        simp only [circuit_norm]
        rw [hval, iha n env c hc h1', ihb _ env c hc h2a']

end StandardECDSA.Gadgets
