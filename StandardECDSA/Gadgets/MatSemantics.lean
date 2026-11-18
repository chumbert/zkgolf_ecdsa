/-
# Semantic soundness of the `mat` lowering

`mat e` allocates one wire per non-constant product of `e` and constrains each
wire to the corresponding product.  This file proves the semantic statement that
the rest of the gadget soundness proofs consume: **any** assignment satisfying
the rows of `mat e` makes the output expression evaluate to the value of `e`.

Task T05 (semantic half).
-/

import StandardECDSA.Gadgets.MatExplicit

namespace StandardECDSA.Gadgets

/-- `ConstraintsHold` splits over concatenation. -/
theorem constraintsHold_append {ops ops' : Operations Fp} {env : Environment Fp} :
    Operations.ConstraintsHold env (ops ++ ops') ↔
      Operations.ConstraintsHold env ops ∧ Operations.ConstraintsHold env ops' := by
  simp only [Operations.ConstraintsHold, Operations.constraints_append, Operations.lookups_append,
    List.mem_append, forall_and, or_imp]
  tauto

theorem mat_eval (e : E) : ∀ n (env : Environment Fp),
    Operations.ConstraintsHold env ((mat e) n).2 →
    Expression.eval env (matOut e n) = Expression.eval env e := by
  induction e with
  | var v =>
      intro n env _
      rfl
  | const c =>
      intro n env _
      rfl
  | add a b iha ihb =>
      intro n env h
      rw [mat_operations_eq] at h
      rw [matOps, constraintsHold_append] at h
      have h1 : Operations.ConstraintsHold env ((mat a) n).2 := by
        rw [mat_operations_eq]; exact h.1
      have h2 : Operations.ConstraintsHold env ((mat b) (n + matLen a)).2 := by
        rw [mat_operations_eq]; exact h.2
      rw [matOut]
      simp only [circuit_norm, iha n env h1, ihb _ env h2]
  | mul a b iha ihb =>
      intro n env h
      rw [mat_operations_eq] at h
      rw [matOps, constraintsHold_append] at h
      obtain ⟨h1, h2⟩ := h
      have h1' : Operations.ConstraintsHold env ((mat a) n).2 := by
        rw [mat_operations_eq]; exact h1
      by_cases hc : deg a = 0 ∨ deg b = 0
      · rw [if_pos hc] at h2
        rw [constraintsHold_append] at h2
        have h2' : Operations.ConstraintsHold env ((mat b) (n + matLen a)).2 := by
          rw [mat_operations_eq]; exact h2.1
        rw [matOut, if_pos hc]
        simp only [circuit_norm, iha n env h1', ihb _ env h2']
      · rw [if_neg hc] at h2
        rw [constraintsHold_append] at h2
        obtain ⟨h2a, h2b⟩ := h2
        have h2a' : Operations.ConstraintsHold env ((mat b) (n + matLen a)).2 := by
          rw [mat_operations_eq]; exact h2a
        have h2c : Expression.eval env
            (matOut a n * matOut b (n + matLen a) - var ⟨n + matLen a + matLen b⟩) = 0 :=
          h2b.1 _ (by simp [Operations.constraints])
        have hrow : Expression.eval env (matOut a n) * Expression.eval env (matOut b (n + matLen a))
            - env.get (n + matLen a + matLen b) = 0 := by
          simpa only [circuit_norm] using h2c
        have hval : env.get (n + matLen a + matLen b)
            = Expression.eval env (matOut a n) * Expression.eval env (matOut b (n + matLen a)) :=
          (sub_eq_zero.mp hrow).symm
        rw [matOut, if_neg hc]
        simp only [circuit_norm]
        rw [hval, iha n env h1', ihb _ env h2a']

end StandardECDSA.Gadgets
