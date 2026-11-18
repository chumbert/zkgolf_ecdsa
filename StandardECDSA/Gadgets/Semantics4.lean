/-
# Semantic specs for `isOnCurve` and `pointEquality`

Both gadgets are *field-level assertions*: their rows say that a polynomial
vanishes.  The semantic spec is the curve equation (resp. projective equality),
and the proof goes through the value lemmas for `mat` and `assertZeroLazy`:
`mat` preserves the value of its argument, and `assertZeroLazy e` forces
`eval e = 0`.

Task T05 (semantic half).
-/

import StandardECDSA.Gadgets.CurveExplicit
import StandardECDSA.Gadgets.Semantics3

namespace StandardECDSA.Gadgets

open WeierstrassCurve

/-! ## Extracting assertion rows from `forAllNoOffset`

`Operations.forAllNoOffset_iff_forall_mem` only exposes the *shallow*
constraints, while the value lemmas `matOut_eval` / `azl_eval` consume
`Operations.constraints` (which also descends into subcircuits).  For the
subcircuit-free operation lists produced by `mat` and `assertZeroLazy` the two
coincide; the following lemma records that fact in the form we need.
-/

theorem forAllNoOffset_constraints {c : ConditionNoOffset Fp} :
    ∀ (ops : Operations Fp), Operations.forAllNoOffset c ops →
      (∀ s ∈ Operations.subcircuits ops, False) →
      ∀ e ∈ Operations.constraints ops, c.assert e
  | [], _, _, e, he => by simp [Operations.constraints] at he
  | .witness _ _ :: ops, h, hf, e, he =>
      forAllNoOffset_constraints ops h.2 (fun s hs => hf s (by simpa [Operations.subcircuits] using hs)) e he
  | .assert a :: ops, h, hf, e, he => by
      simp only [Operations.constraints, List.mem_cons] at he
      rcases he with rfl | he
      · exact h.1
      · exact forAllNoOffset_constraints ops h.2
          (fun s hs => hf s (by simpa [Operations.subcircuits] using hs)) e he
  | .lookup _ :: ops, h, hf, e, he =>
      forAllNoOffset_constraints ops h.2 (fun s hs => hf s (by simpa [Operations.subcircuits] using hs)) e he
  | .interact _ :: ops, h, hf, e, he =>
      forAllNoOffset_constraints ops h.2 (fun s hs => hf s (by simpa [Operations.subcircuits] using hs)) e he
  | .subcircuit s :: ops, h, hf, e, he =>
      (hf ⟨_, s⟩ (by simp [Operations.subcircuits])).elim

/-- A `forAllNoOffset` whose condition is everywhere true holds for every
operation list.  Used to discharge the `Operations.Requirements` half of
`FormalAssertion.Soundness` for the field gadgets, which emit no interactions. -/
theorem forAllNoOffset_true {c : ConditionNoOffset Fp}
    (hw : ∀ (m : ℕ) (c' : WitgenIR Fp m), c.witness m c')
    (ha : ∀ e, c.assert e) (hl : ∀ l, c.lookup l) (hi : ∀ i, c.interact i)
    (hsub : ∀ {m} (s : Subcircuit Fp m), c.subcircuit s) :
    ∀ ops : Operations Fp, Operations.forAllNoOffset c ops
  | [] => trivial
  | .witness m c' :: ops => ⟨hw m c', forAllNoOffset_true hw ha hl hi hsub ops⟩
  | .assert e :: ops => ⟨ha _, forAllNoOffset_true hw ha hl hi hsub ops⟩
  | .lookup l :: ops => ⟨hl _, forAllNoOffset_true hw ha hl hi hsub ops⟩
  | .interact i :: ops => ⟨hi _, forAllNoOffset_true hw ha hl hi hsub ops⟩
  | .subcircuit s :: ops => ⟨hsub s, forAllNoOffset_true hw ha hl hi hsub ops⟩

/-- `Operations.Requirements` is vacuous for an operation list with no
interactions and no subcircuits. -/
theorem requirements_of_nil (env : Environment Fp) :
    ∀ (ops : Operations Fp), Operations.interactions ops = [] →
      (∀ s ∈ Operations.subcircuits ops, False) → Operations.Requirements env ops
  | [], _, _ => trivial
  | .witness _ _ :: ops, h, hf => by
      have ih := requirements_of_nil env ops (by simpa [Operations.interactions] using h)
        (fun s hs => hf s (by simpa [Operations.subcircuits] using hs))
      simpa [Operations.Requirements, Operations.forAllNoOffset] using ih
  | .assert _ :: ops, h, hf => by
      have ih := requirements_of_nil env ops (by simpa [Operations.interactions] using h)
        (fun s hs => hf s (by simpa [Operations.subcircuits] using hs))
      simpa [Operations.Requirements, Operations.forAllNoOffset] using ih
  | .lookup _ :: ops, h, hf => by
      have ih := requirements_of_nil env ops (by simpa [Operations.interactions] using h)
        (fun s hs => hf s (by simpa [Operations.subcircuits] using hs))
      simpa [Operations.Requirements, Operations.forAllNoOffset] using ih
  | .interact _ :: ops, h, _ => by
      simp [Operations.Requirements, Operations.forAllNoOffset, Operations.interactions] at h
  | .subcircuit s :: ops, _, hf => (hf ⟨_, s⟩ (by simp [Operations.subcircuits])).elim

/-! ### Subcircuit-freeness of the field gadgets

`mat` and `assertZeroLazy` only ever emit `witness` and `assert` operations, so
their `Operations.subcircuits` list is empty.  This is what lets
`forAllNoOffset_constraints` be applied to them.
-/

theorem matOps_subcircuits (e : E) : ∀ n, Operations.subcircuits (matOps e n) = [] := by
  induction e with
  | var v => intro n; rfl
  | const c => intro n; rfl
  | add a b iha ihb =>
      intro n; simp [matOps, Operations.subcircuits_append, iha, ihb]
  | mul a b iha ihb =>
      intro n
      simp only [matOps, iha, ihb, List.nil_append]
      split <;> simp [Operations.subcircuits, Operations.subcircuits_append, iha, ihb]

theorem mat_subcircuits (e : E) : ∀ n, Operations.subcircuits ((mat e) n).2 = [] := by
  induction e with
  | var v => intro n; rfl
  | const c => intro n; rfl
  | add a b iha ihb =>
      intro n
      simp [mat, bind_snd, pure_snd, map_snd, Operations.subcircuits_append, iha, ihb]
  | mul a b iha ihb =>
      intro n
      simp only [mat, bind_snd, pure_snd, witnessField_snd, assertZero_snd,
        List.nil_append, iha, ihb]
      split <;> simp [Operations.subcircuits, Operations.subcircuits_append, iha, ihb,
        pure_snd, bind_snd, map_snd, witnessField_snd, assertZero_snd]

theorem azlLoop_subcircuits (acc : E) :
    ∀ (l : List (Fp × E)) n, Operations.subcircuits ((azlLoop acc l n).2) = [] := by
  intro l
  induction l generalizing acc with
  | nil => intro n; rfl
  | cons it rest ih =>
      intro n
      obtain ⟨c, t⟩ := it
      simp [azlLoop, bind_snd, Operations.subcircuits_append, ih, mat_subcircuits]

theorem azlLinLoop_subcircuits (acc : E) :
    ∀ (l : List (Fp × E)) n, Operations.subcircuits ((azlLinLoop acc l n).2) = [] := by
  intro l
  induction l generalizing acc with
  | nil => intro n; rfl
  | cons it rest ih =>
      intro n
      obtain ⟨c, t⟩ := it
      simp only [azlLinLoop, ih]

theorem assertZeroLazy_subcircuits (e : E) :
    ∀ n, Operations.subcircuits ((assertZeroLazy e n).2) = [] := by
  intro n
  cases hf : (List.filter (fun it => isProd it.2) (flat 1 e)) with
  | nil =>
      simp only [assertZeroLazy, hf, assertZero_snd, Operations.subcircuits]
  | cons it rest =>
      obtain ⟨c, t⟩ := it
      cases t with
      | mul a b =>
          simp [assertZeroLazy, hf, bind_snd, Operations.subcircuits,
            Operations.subcircuits_append, azlLoop_subcircuits,
            azlLinLoop_subcircuits, assertZero_snd, mat_subcircuits]
      | var v => simp [assertZeroLazy, hf, pure_snd, Operations.subcircuits]
      | const k => simp [assertZeroLazy, hf, pure_snd, Operations.subcircuits]
      | add x y => simp [assertZeroLazy, hf, pure_snd, Operations.subcircuits]

/-! ### Interaction-freeness of the field gadgets -/

theorem matOps_interactions (e : E) : ∀ n, Operations.interactions (matOps e n) = [] := by
  induction e with
  | var v => intro n; rfl
  | const c => intro n; rfl
  | add a b iha ihb =>
      intro n; simp [matOps, Operations.interactions_append, iha, ihb]
  | mul a b iha ihb =>
      intro n
      simp only [matOps, iha, ihb, List.nil_append]
      split <;> simp [Operations.interactions, Operations.interactions_append, iha, ihb]

theorem mat_interactions (e : E) : ∀ n, Operations.interactions ((mat e) n).2 = [] := by
  induction e with
  | var v => intro n; rfl
  | const c => intro n; rfl
  | add a b iha ihb =>
      intro n
      simp [mat, bind_snd, pure_snd, map_snd, Operations.interactions_append, iha, ihb]
  | mul a b iha ihb =>
      intro n
      simp only [mat, bind_snd, pure_snd, witnessField_snd, assertZero_snd,
        List.nil_append, iha, ihb]
      split <;> simp [Operations.interactions, Operations.interactions_append, iha, ihb,
        pure_snd, bind_snd, map_snd, witnessField_snd, assertZero_snd]

theorem azlLoop_interactions (acc : E) :
    ∀ (l : List (Fp × E)) n, Operations.interactions ((azlLoop acc l n).2) = [] := by
  intro l
  induction l generalizing acc with
  | nil => intro n; rfl
  | cons it rest ih =>
      intro n
      obtain ⟨c, t⟩ := it
      simp [azlLoop, bind_snd, Operations.interactions_append, ih, mat_interactions]

theorem azlLinLoop_interactions (acc : E) :
    ∀ (l : List (Fp × E)) n, Operations.interactions ((azlLinLoop acc l n).2) = [] := by
  intro l
  induction l generalizing acc with
  | nil => intro n; rfl
  | cons it rest ih =>
      intro n
      obtain ⟨c, t⟩ := it
      simp only [azlLinLoop, ih]

theorem assertZeroLazy_interactions (e : E) :
    ∀ n, Operations.interactions ((assertZeroLazy e n).2) = [] := by
  intro n
  cases hf : (List.filter (fun it => isProd it.2) (flat 1 e)) with
  | nil => simp [assertZeroLazy, hf, assertZero_snd, Operations.interactions]
  | cons it rest =>
      obtain ⟨c, t⟩ := it
      cases t with
      | mul a b =>
          simp [assertZeroLazy, hf, bind_snd, Operations.interactions,
            Operations.interactions_append, azlLoop_interactions,
            azlLinLoop_interactions, assertZero_snd, mat_interactions]
      | var v => simp [assertZeroLazy, hf, pure_snd, Operations.interactions]
      | const k => simp [assertZeroLazy, hf, pure_snd, Operations.interactions]
      | add x y => simp [assertZeroLazy, hf, pure_snd, Operations.interactions]

/-! ## Weighted sums over flattened expressions -/

/-- Weighted sum of a flattened expression. -/
def flatSum (env : Environment Fp) (l : List (Fp × E)) : Fp :=
  (l.map (fun it => it.1 * Expression.eval env it.2)).sum

theorem flatSum_append (env : Environment Fp) (l₁ l₂ : List (Fp × E)) :
    flatSum env (l₁ ++ l₂) = flatSum env l₁ + flatSum env l₂ := by
  simp [flatSum, List.map_append, List.sum_append]

theorem flatSum_filter (env : Environment Fp) (p : Fp × E → Bool) (l : List (Fp × E)) :
    flatSum env l = flatSum env (l.filter p) + flatSum env (l.filter (fun x => !p x)) := by
  induction l with
  | nil => simp [flatSum]
  | cons a t ih =>
      cases hp : p a with
      | true =>
          simp only [List.filter_cons, hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            flatSum, List.map_cons, List.sum_cons] at ih ⊢
          rw [ih]; ring
      | false =>
          simp only [List.filter_cons, hp, Bool.not_false, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, flatSum, List.map_cons, List.sum_cons] at ih ⊢
          rw [ih]; ring

/-- A degree-zero expression evaluates to its constant value. -/
theorem eval_eq_constVal {e : E} (h : deg e = 0) (env : Environment Fp) :
    Expression.eval env e = constVal e := by
  induction e with
  | var v => simp [deg, Challenge.CostR1CS.degree] at h
  | const c => rfl
  | add a b iha ihb =>
      simp only [deg, Challenge.CostR1CS.degree, Nat.max_eq_zero_iff] at h
      simp only [constVal, Expression.eval] at iha ihb ⊢
      rw [iha h.1, ihb h.2]
  | mul a b iha ihb =>
      simp only [deg, Challenge.CostR1CS.degree, Nat.add_eq_zero_iff] at h
      simp only [constVal, Expression.eval] at iha ihb ⊢
      rw [iha h.1, ihb h.2]

/-- `flat` preserves the value of the expression. -/
theorem flatSum_flat (env : Environment Fp) (c : Fp) (e : E) :
    flatSum env (flat c e) = c * Expression.eval env e := by
  induction e generalizing c with
  | var v => simp [flat, flatSum]
  | const k => simp [flat, flatSum]
  | add a b iha ihb =>
      simp only [flat, flatSum_append, iha, ihb, Expression.eval]
      ring
  | mul a b iha ihb =>
      by_cases h1 : deg a = 0
      · simp only [flat, h1, ↓reduceIte]
        rw [ihb, ← eval_eq_constVal h1 env]
        simp only [Expression.eval]
        ring
      · by_cases h2 : deg b = 0
        · simp only [flat, h1, h2, ↓reduceIte]
          rw [iha, ← eval_eq_constVal h2 env]
          simp only [Expression.eval]
          ring
        · simp only [flat, h1, h2, ↓reduceIte, flatSum, List.map_cons, List.sum_cons,
            List.map_nil, List.sum_nil, Expression.eval]
          ring

/-- Every item of the product-filtered flattening is a genuine product. -/
theorem flat_filter_isProd (c : Fp) (e : E) :
    ∀ it ∈ (flat c e).filter (fun it => isProd it.2), ∃ a b : E, it.2 = .mul a b := by
  induction e generalizing c with
  | var v => simp [flat, isProd]
  | const k => simp [flat, isProd]
  | add a b iha ihb =>
      intro it hit
      simp only [flat, List.filter_append, List.mem_append] at hit
      rcases hit with h | h
      · exact iha c it h
      · exact ihb c it h
  | mul a b iha ihb =>
      intro it hit
      by_cases h1 : deg a = 0
      · simp only [flat, h1, ↓reduceIte] at hit
        exact ihb _ it hit
      · by_cases h2 : deg b = 0
        · simp only [flat, h1, h2, ↓reduceIte] at hit
          exact iha _ it hit
        · simp only [flat, h1, h2, ↓reduceIte, List.filter_cons, isProd, List.mem_cons,
            List.mem_singleton] at hit
          rcases hit with rfl | h
          · exact ⟨a, b, rfl⟩
          · simp at h

/-! ## `mat` preserves the value -/

theorem matOut_eval (env : Environment Fp) (e : E) :
    ∀ n, (∀ c ∈ Operations.constraints (matOps e n), Expression.eval env c = 0) →
      Expression.eval env (matOut e n) = Expression.eval env e := by
  induction e with
  | var v => intro n _; rfl
  | const k => intro n _; rfl
  | add a b iha ihb =>
      intro n h
      have h1 : ∀ c ∈ Operations.constraints (matOps a n), Expression.eval env c = 0 :=
        fun c hc => h c (by
          simp only [matOps, Operations.constraints_append, List.mem_append]; exact Or.inl hc)
      have h2 : ∀ c ∈ Operations.constraints (matOps b (n + matLen a)),
          Expression.eval env c = 0 :=
        fun c hc => h c (by
          simp only [matOps, Operations.constraints_append, List.mem_append]; exact Or.inr hc)
      simp only [matOut, Expression.eval, iha n h1, ihb _ h2]
  | mul a b iha ihb =>
      intro n h
      by_cases h1 : deg a = 0 ∨ deg b = 0
      · have hA : ∀ c ∈ Operations.constraints (matOps a n), Expression.eval env c = 0 :=
          fun c hc => h c (by
            simp only [matOps, h1, ↓reduceIte, Operations.constraints_append, List.mem_append]
            exact Or.inl hc)
        have hB : ∀ c ∈ Operations.constraints (matOps b (n + matLen a)),
            Expression.eval env c = 0 :=
          fun c hc => h c (by
            simp only [matOps, h1, ↓reduceIte, Operations.constraints_append, List.mem_append]
            exact Or.inr (Or.inl hc))
        simp only [matOut, h1, ↓reduceIte, Expression.eval, iha n hA, ihb _ hB]
      · have hA : ∀ c ∈ Operations.constraints (matOps a n), Expression.eval env c = 0 :=
          fun c hc => h c (by
            simp only [matOps, h1, ↓reduceIte, Operations.constraints_append, List.mem_append]
            exact Or.inl hc)
        have hB : ∀ c ∈ Operations.constraints (matOps b (n + matLen a)),
            Expression.eval env c = 0 :=
          fun c hc => h c (by
            simp only [matOps, h1, ↓reduceIte, Operations.constraints_append, List.mem_append]
            exact Or.inr (Or.inl hc))
        have hC : Expression.eval env
            (matOut a n * matOut b (n + matLen a) - .var ⟨n + matLen a + matLen b⟩) = 0 :=
          h _ (by
            simp only [matOps, h1, ↓reduceIte, Operations.constraints_append, List.mem_append,
              Operations.constraints, List.mem_cons, List.mem_singleton]
            exact Or.inr (Or.inr (Or.inl trivial)))
        simp only [matOut, h1, ↓reduceIte] at hC ⊢
        simp only [circuit_norm] at hC ⊢
        rw [iha n hA, ihb _ hB] at hC
        linear_combination -hC

/-! ## `assertZeroLazy` forces zero -/

theorem azlLoop_eval (env : Environment Fp) (acc : E) (l : List (Fp × E)) :
    ∀ n, (∀ c ∈ Operations.constraints ((azlLoop acc l n).2), Expression.eval env c = 0) →
      Expression.eval env ((azlLoop acc l n).1) = Expression.eval env acc + flatSum env l := by
  induction l generalizing acc with
  | nil =>
      intro n _
      simp [azlLoop, pure_fst, flatSum]
  | cons it rest ih =>
      intro n h
      obtain ⟨c, t⟩ := it
      have hA : ∀ c' ∈ Operations.constraints ((mat t n).2), Expression.eval env c' = 0 :=
        fun c' hc => h c' (by
          simp only [azlLoop, bind_snd, Operations.constraints_append, List.mem_append]
          exact Or.inl hc)
      have hB : ∀ c' ∈ Operations.constraints ((azlLoop (acc + sc c ((mat t n).1)) rest
          (n + Operations.localLength ((mat t n).2))).2), Expression.eval env c' = 0 :=
        fun c' hc => h c' (by
          simp only [azlLoop, bind_snd, Operations.constraints_append, List.mem_append]
          exact Or.inr hc)
      have hmat : Expression.eval env ((mat t n).1) = Expression.eval env t := by
        rw [mat_output_eq]
        exact matOut_eval env t n (by rwa [mat_operations_eq] at hA)
      simp only [azlLoop, bind_fst, List.map_cons, List.sum_cons]
      rw [ih (acc + sc c ((mat t n).1)) (n + Operations.localLength ((mat t n).2)) hB]
      simp only [flatSum, List.map_cons, List.sum_cons, sc, Expression.eval, hmat]
      ring

theorem azlLinLoop_eval (env : Environment Fp) (acc : E) (l : List (Fp × E)) :
    ∀ n, Expression.eval env ((azlLinLoop acc l n).1) = Expression.eval env acc + flatSum env l := by
  induction l generalizing acc with
  | nil => intro n; simp [azlLinLoop, pure_fst, flatSum]
  | cons it rest ih =>
      intro n
      obtain ⟨c, t⟩ := it
      simp only [azlLinLoop, List.map_cons, List.sum_cons]
      rw [ih]
      simp only [flatSum, List.map_cons, List.sum_cons, sc, Expression.eval]
      ring

theorem azl_eval (env : Environment Fp) (e : E) :
    ∀ n, (∀ c ∈ Operations.constraints ((assertZeroLazy e n).2), Expression.eval env c = 0) →
      Expression.eval env e = 0 := by
  intro n h
  cases hf : (flat 1 e).filter (fun it => isProd it.2) with
  | nil =>
      exact h e (by
        simp only [assertZeroLazy, hf, assertZero_snd, Operations.constraints,
          List.mem_cons, List.mem_singleton]
        exact Or.inl trivial)
  | cons it rest =>
      obtain ⟨c, t⟩ := it
      obtain ⟨a, b, hab⟩ := flat_filter_isProd 1 e (c, t)
        (by rw [hf]; exact List.mem_cons_self ..)
      have hab' : t = .mul a b := hab
      simp only [hab'] at hf
      have hA : ∀ c' ∈ Operations.constraints ((mat a n).2), Expression.eval env c' = 0 := by
        intro c' hc
        refine h c' ?_
        simp only [assertZeroLazy, hf, bind_snd, Operations.constraints_append, List.mem_append]
        exact Or.inl hc
      have hB : ∀ c' ∈ Operations.constraints
          ((mat b (n + Operations.localLength ((mat a n).2))).2), Expression.eval env c' = 0 := by
        intro c' hc
        refine h c' ?_
        simp only [assertZeroLazy, hf, bind_snd, Operations.constraints_append, List.mem_append]
        exact Or.inr (Or.inl hc)
      have hC : ∀ c' ∈ Operations.constraints
          ((azlLoop (sc c (.mul ((mat a n).1)
              ((mat b (n + Operations.localLength ((mat a n).2))).1))) rest
            (n + Operations.localLength ((mat a n).2) +
              Operations.localLength ((mat b (n + Operations.localLength ((mat a n).2))).2))).2),
          Expression.eval env c' = 0 := by
        intro c' hc
        refine h c' ?_
        simp only [assertZeroLazy, hf, bind_snd, Operations.constraints_append, List.mem_append]
        exact Or.inr (Or.inr (Or.inl hc))
      have hD : Expression.eval env
          ((azlLinLoop (azlLoop (sc c (.mul ((mat a n).1)
              ((mat b (n + Operations.localLength ((mat a n).2))).1))) rest
            (n + Operations.localLength ((mat a n).2) +
              Operations.localLength ((mat b (n + Operations.localLength ((mat a n).2))).2))).1)
            ((flat 1 e).filter (fun it => !isProd it.2))
            (n + Operations.localLength ((mat a n).2) +
              Operations.localLength ((mat b (n + Operations.localLength ((mat a n).2))).2) +
              Operations.localLength
                ((azlLoop (sc c (.mul ((mat a n).1)
                    ((mat b (n + Operations.localLength ((mat a n).2))).1))) rest
                  (n + Operations.localLength ((mat a n).2) +
                    Operations.localLength
                      ((mat b (n + Operations.localLength ((mat a n).2))).2))).2))).1 = 0 := by
        refine h _ ?_
        simp only [assertZeroLazy, hf, bind_snd, Operations.constraints_append, List.mem_append,
          Operations.constraints, List.mem_cons, List.mem_singleton]
        tauto
      have hmatA : Expression.eval env ((mat a n).1) = Expression.eval env a := by
        rw [mat_output_eq]
        exact matOut_eval env a n (by rwa [mat_operations_eq] at hA)
      have hmatB : Expression.eval env
          ((mat b (n + Operations.localLength ((mat a n).2))).1) = Expression.eval env b := by
        rw [mat_output_eq]
        exact matOut_eval env b _ (by rwa [mat_operations_eq] at hB)
      have hloop := azlLoop_eval env (sc c (.mul ((mat a n).1)
        ((mat b (n + Operations.localLength ((mat a n).2))).1))) rest
        (n + Operations.localLength ((mat a n).2) +
          Operations.localLength ((mat b (n + Operations.localLength ((mat a n).2))).2)) hC
      have hlin := azlLinLoop_eval env
        ((azlLoop (sc c (.mul ((mat a n).1)
          ((mat b (n + Operations.localLength ((mat a n).2))).1))) rest
          (n + Operations.localLength ((mat a n).2) +
            Operations.localLength ((mat b (n + Operations.localLength ((mat a n).2))).2))).1)
        ((flat 1 e).filter (fun it => !isProd it.2))
        (n + Operations.localLength ((mat a n).2) +
          Operations.localLength ((mat b (n + Operations.localLength ((mat a n).2))).2) +
          Operations.localLength
            ((azlLoop (sc c (.mul ((mat a n).1)
                ((mat b (n + Operations.localLength ((mat a n).2))).1))) rest
              (n + Operations.localLength ((mat a n).2) +
                Operations.localLength
                  ((mat b (n + Operations.localLength ((mat a n).2))).2))).2))
      rw [hlin] at hD
      rw [hloop] at hD
      simp only [sc, Expression.eval] at hD
      rw [hmatA, hmatB] at hD
      have hflat := flatSum_flat env 1 e
      have hsplit := flatSum_filter env (fun it => isProd it.2) (flat 1 e)
      rw [hf] at hsplit
      simp only [flatSum, List.map_cons, List.sum_cons, Expression.eval] at hsplit hflat
      rw [hflat] at hsplit
      simp only [one_mul] at hsplit
      simp only [flatSum] at hD ⊢
      linear_combination hsplit + hD


/-! ## Channel metadata for subcircuit- and interaction-free operation lists -/

theorem subcircuitChannelsWithRequirements_eq_nil {ops : Operations Fp}
    (h : ∀ s ∈ Operations.subcircuits ops, False) :
    Operations.subcircuitChannelsWithRequirements ops = [] := by
  induction ops using Operations.induct with
  | empty => rfl
  | witness m c ops ih =>
      simp only [Operations.subcircuitChannelsWithRequirements, List.map_cons,
        List.flatten_cons, List.nil_append]
      exact ih (fun s hs => h s (by simp [Operations.subcircuits, hs]))
  | assert e ops ih =>
      simp only [Operations.subcircuitChannelsWithRequirements, List.map_cons,
        List.flatten_cons, List.nil_append]
      exact ih (fun s hs => h s (by simp [Operations.subcircuits, hs]))
  | lookup l ops ih =>
      simp only [Operations.subcircuitChannelsWithRequirements, List.map_cons,
        List.flatten_cons, List.nil_append]
      exact ih (fun s hs => h s (by simp [Operations.subcircuits, hs]))
  | interact i ops ih =>
      simp only [Operations.subcircuitChannelsWithRequirements, List.map_cons,
        List.flatten_cons, List.nil_append]
      exact ih (fun s hs => h s (by simp [Operations.subcircuits, hs]))
  | subcircuit s ops ih =>
      exact (h ⟨_, s⟩ (by simp [Operations.subcircuits])).elim

theorem shallowChannels_eq_nil {ops : Operations Fp}
    (h : Operations.interactions ops = []) : Operations.shallowChannels ops = [] := by
  induction ops using Operations.induct with
  | empty => rfl
  | witness m c ops ih =>
      simp only [Operations.shallowChannels, List.map_cons, List.flatten_cons,
        List.nil_append]
      exact ih (by simpa [Operations.interactions] using h)
  | assert e ops ih =>
      simp only [Operations.shallowChannels, List.map_cons, List.flatten_cons,
        List.nil_append]
      exact ih (by simpa [Operations.interactions] using h)
  | lookup l ops ih =>
      simp only [Operations.shallowChannels, List.map_cons, List.flatten_cons,
        List.nil_append]
      exact ih (by simpa [Operations.interactions] using h)
  | interact i ops ih =>
      simp [Operations.interactions] at h
  | subcircuit s ops ih =>
      simp only [Operations.shallowChannels, List.map_cons, List.flatten_cons,
        List.nil_append]
      exact ih (by
        have hh := h
        simp only [Operations.interactions, List.append_eq_nil_iff] at hh
        exact hh.2)

/-- Pointwise monotonicity of `forAllNoOffset`. -/
theorem forAllNoOffset_mono {c c' : ConditionNoOffset Fp}
    (hw : ∀ (m : ℕ) (c'' : WitgenIR Fp m), c.witness m c'' → c'.witness m c'')
    (ha : ∀ e, c.assert e → c'.assert e) (hl : ∀ l, c.lookup l → c'.lookup l)
    (hi : ∀ i, c.interact i → c'.interact i)
    (hs : ∀ {m} (s : Subcircuit Fp m), c.subcircuit s → c'.subcircuit s) :
    ∀ ops : Operations Fp, Operations.forAllNoOffset c ops → Operations.forAllNoOffset c' ops
  | [], _ => trivial
  | .witness m c'' :: ops, h =>
      ⟨hw _ _ h.1, forAllNoOffset_mono hw ha hl hi hs ops h.2⟩
  | .assert e :: ops, h => ⟨ha _ h.1, forAllNoOffset_mono hw ha hl hi hs ops h.2⟩
  | .lookup l :: ops, h => ⟨hl _ h.1, forAllNoOffset_mono hw ha hl hi hs ops h.2⟩
  | .interact i :: ops, h => ⟨hi _ h.1, forAllNoOffset_mono hw ha hl hi hs ops h.2⟩
  | .subcircuit s :: ops, h => ⟨hs s h.1, forAllNoOffset_mono hw ha hl hi hs ops h.2⟩

/-- `InChannelsOrRequirements` with an empty channel list is vacuous for an
operation list with no interactions and no subcircuits. -/
theorem inChannelsOrRequirements_nil (env : Environment Fp) :
    ∀ (ops : Operations Fp), Operations.interactions ops = [] →
      (∀ s ∈ Operations.subcircuits ops, False) →
      Operations.InChannelsOrRequirements [] env ops
  | [], _, _ => trivial
  | .witness _ _ :: ops, h, hf => by
      have ih := inChannelsOrRequirements_nil env ops
        (by simpa [Operations.interactions] using h)
        (fun s hs => hf s (by simpa [Operations.subcircuits] using hs))
      simpa [Operations.InChannelsOrRequirements, Operations.forAllNoOffset] using ih
  | .assert _ :: ops, h, hf => by
      have ih := inChannelsOrRequirements_nil env ops
        (by simpa [Operations.interactions] using h)
        (fun s hs => hf s (by simpa [Operations.subcircuits] using hs))
      simpa [Operations.InChannelsOrRequirements, Operations.forAllNoOffset] using ih
  | .lookup _ :: ops, h, hf => by
      have ih := inChannelsOrRequirements_nil env ops
        (by simpa [Operations.interactions] using h)
        (fun s hs => hf s (by simpa [Operations.subcircuits] using hs))
      simpa [Operations.InChannelsOrRequirements, Operations.forAllNoOffset] using ih
  | .interact _ :: ops, h, _ => by simp [Operations.interactions] at h
  | .subcircuit s :: ops, _, hf => (hf ⟨_, s⟩ (by simp [Operations.subcircuits])).elim

/-- `RequirementsChannelsLawful` is automatic for an operation list with no
subcircuits and no interactions. -/
theorem requirementsChannelsLawful_of_nil {ops : Operations Fp}
    (hsub : ∀ s ∈ Operations.subcircuits ops, False)
    (hint : Operations.interactions ops = []) :
    Operations.RequirementsChannelsLawful ops [] [] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [subcircuitChannelsWithRequirements_eq_nil hsub]
  · intro c hc
    exact absurd hc (by simp [shallowChannels_eq_nil hint])
  · exact fun env _ => inChannelsOrRequirements_nil env ops hint hsub

/-! ## Completeness lemmas for `mat` and `assertZeroLazy` -/

/-- Bridge: `ConstraintsHold.Completeness` gives vanishing of every constraint row. -/
theorem constraints_eval_of_complete {env : ProverEnvironment Fp} {ops : Operations Fp}
    (h : ConstraintsHold.Completeness env ops)
    (hsub : ∀ s ∈ Operations.subcircuits ops, False) :
    ∀ e ∈ Operations.constraints ops, Expression.eval env.toEnvironment e = 0 :=
  forAllNoOffset_constraints ops h hsub

theorem matOut_eval_complete (env : ProverEnvironment Fp) (e : E) :
    ∀ n, env.UsesLocalWitnessesCompleteness n (matOps e n) →
      Expression.eval env.toEnvironment (matOut e n) = Expression.eval env.toEnvironment e := by
  intro n h
  exact matOut_eval env.toEnvironment e n
    (constraints_eval_of_complete (mat_complete e n env h)
      (by rw [matOps_subcircuits]; simp))

theorem azlLoop_eval_complete (env : ProverEnvironment Fp) (acc : E) (l : List (Fp × E)) :
    ∀ n, env.UsesLocalWitnessesCompleteness n ((azlLoop acc l n).2) →
      Expression.eval env.toEnvironment ((azlLoop acc l n).1) =
        Expression.eval env.toEnvironment acc + flatSum env.toEnvironment l := by
  induction l generalizing acc with
  | nil => intro n _; simp [azlLoop, pure_fst, flatSum]
  | cons it rest ih =>
      intro n h
      obtain ⟨c, t⟩ := it
      simp only [azlLoop, bind_snd] at h
      rw [ulwc_append] at h
      obtain ⟨hA, hB⟩ := h
      have hmat : Expression.eval env.toEnvironment ((mat t n).1)
          = Expression.eval env.toEnvironment t := by
        rw [mat_output_eq]
        exact matOut_eval_complete env t n (by rwa [mat_operations_eq] at hA)
      simp only [azlLoop, bind_fst, List.map_cons, List.sum_cons]
      rw [ih (acc + sc c ((mat t n).1)) (n + Operations.localLength ((mat t n).2)) hB]
      simp only [flatSum, List.map_cons, List.sum_cons, sc, Expression.eval, hmat]
      ring

theorem azlLinLoop_eval_complete (env : ProverEnvironment Fp) (acc : E) (l : List (Fp × E)) :
    ∀ n, Expression.eval env.toEnvironment ((azlLinLoop acc l n).1) =
      Expression.eval env.toEnvironment acc + flatSum env.toEnvironment l :=
  azlLinLoop_eval env.toEnvironment acc l

theorem azlLoop_complete (acc : E) :
    ∀ (l : List (Fp × E)) n (env : ProverEnvironment Fp),
      env.UsesLocalWitnessesCompleteness n ((azlLoop acc l n).2) →
      ConstraintsHold.Completeness env ((azlLoop acc l n).2) := by
  intro l
  induction l generalizing acc with
  | nil => intro n env _; simp [azlLoop, pure_snd, ConstraintsHold.Completeness,
      Operations.forAllNoOffset]
  | cons it rest ih =>
      intro n env h
      obtain ⟨c, t⟩ := it
      simp only [azlLoop, bind_snd] at h
      rw [ulwc_append] at h
      obtain ⟨hA, hB⟩ := h
      rw [azlLoop, bind_snd, ConstraintsHold.Completeness, Operations.forAllNoOffset_append]
      refine ⟨?_, ih _ _ env hB⟩
      rw [mat_operations_eq] at hA ⊢
      exact mat_complete t n env hA

theorem azlLinLoop_complete (acc : E) :
    ∀ (l : List (Fp × E)) n (env : ProverEnvironment Fp),
      ConstraintsHold.Completeness env ((azlLinLoop acc l n).2) := by
  intro l
  induction l generalizing acc with
  | nil => intro n env; simp [azlLinLoop, pure_snd, ConstraintsHold.Completeness,
      Operations.forAllNoOffset]
  | cons it rest ih =>
      intro n env
      obtain ⟨c, t⟩ := it
      rw [azlLinLoop]
      exact ih _ _ env

theorem assertZeroLazy_complete (e : E) :
    ∀ n (env : ProverEnvironment Fp),
      env.UsesLocalWitnessesCompleteness n ((assertZeroLazy e n).2) →
      Expression.eval env.toEnvironment e = 0 →
      ConstraintsHold.Completeness env ((assertZeroLazy e n).2) := by
  intro n env h he
  cases hf : (flat 1 e).filter (fun it => isProd it.2) with
  | nil =>
      rw [assertZeroLazy, hf, assertZero_snd]
      simp only [ConstraintsHold.Completeness, Operations.forAllNoOffset]
      exact ⟨he, trivial⟩
  | cons it rest =>
      obtain ⟨c, t⟩ := it
      obtain ⟨a, b, hab⟩ := flat_filter_isProd 1 e (c, t)
        (by rw [hf]; exact List.mem_cons_self ..)
      have hab' : t = .mul a b := hab
      simp only [hab'] at hf
      rw [assertZeroLazy, hf] at h ⊢
      simp only [bind_snd] at h ⊢
      rw [ulwc_append] at h
      obtain ⟨hA, h⟩ := h
      rw [ulwc_append] at h
      obtain ⟨hB, h⟩ := h
      rw [ulwc_append] at h
      obtain ⟨hC, hD⟩ := h
      simp only [ConstraintsHold.Completeness, Operations.forAllNoOffset_append]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [mat_operations_eq] at hA ⊢
        exact mat_complete a n env hA
      · simp only [matOps_localLength, mat_localLength_eq] at hB ⊢
        rw [mat_operations_eq] at hB ⊢
        exact mat_complete b _ env hB
      · exact azlLoop_complete _ rest _ env hC
      · exact azlLinLoop_complete _ _ _ env
      · rw [assertZero_snd]
        simp only [ConstraintsHold.Completeness, Operations.forAllNoOffset]
        have hmatA : Expression.eval env.toEnvironment ((mat a n).1)
            = Expression.eval env.toEnvironment a := by
          rw [mat_output_eq]
          exact matOut_eval_complete env a n (by rw [mat_operations_eq a n] at hA; exact hA)
        have hmatB : Expression.eval env.toEnvironment
            ((mat b (n + Operations.localLength ((mat a n).2))).1)
            = Expression.eval env.toEnvironment b := by
          rw [mat_output_eq]
          exact matOut_eval_complete env b _ (by rw [mat_operations_eq b _] at hB; exact hB)
        have hloop := azlLoop_eval_complete env
          (sc c (.mul ((mat a n).1)
            ((mat b (n + Operations.localLength ((mat a n).2))).1))) rest
          (n + Operations.localLength ((mat a n).2) +
            Operations.localLength ((mat b (n + Operations.localLength ((mat a n).2))).2)) hC
        have hlin := azlLinLoop_eval_complete env
          ((azlLoop (sc c (.mul ((mat a n).1)
            ((mat b (n + Operations.localLength ((mat a n).2))).1))) rest
            (n + Operations.localLength ((mat a n).2) +
              Operations.localLength
                ((mat b (n + Operations.localLength ((mat a n).2))).2))).1)
          ((flat 1 e).filter (fun it => !isProd it.2))
          (n + Operations.localLength ((mat a n).2) +
            Operations.localLength ((mat b (n + Operations.localLength ((mat a n).2))).2) +
            Operations.localLength
              ((azlLoop (sc c (.mul ((mat a n).1)
                  ((mat b (n + Operations.localLength ((mat a n).2))).1))) rest
                (n + Operations.localLength ((mat a n).2) +
                  Operations.localLength
                    ((mat b (n + Operations.localLength ((mat a n).2))).2))).2))
        rw [hlin, hloop]
        simp only [sc, Expression.eval, hmatA, hmatB]
        have hflat := flatSum_flat env.toEnvironment 1 e
        have hsplit := flatSum_filter env.toEnvironment (fun it => isProd it.2) (flat 1 e)
        rw [hf] at hsplit
        simp only [flatSum, List.map_cons, List.sum_cons, Expression.eval] at hsplit hflat
        rw [hflat] at hsplit
        simp only [one_mul] at hsplit
        refine ⟨?_, trivial⟩
        simp only [flatSum]
        rw [← hsplit, he]

/-! ## `isOnCurve` as a `FormalAssertion` -/

/-- Semantic spec of `isOnCurve`: the input is an affine on-curve point. -/
def isOnCurveSpec (i : fields 2 Fp) : Prop := NS i[0] i[1]

theorem isOnCurveMain_soundness :
    FormalAssertion.Soundness Fp isOnCurveMain (fun _ => True) isOnCurveSpec := by
  circuit_proof_start
  simp only [isOnCurveMain, isOnCurve, mm, bind_snd] at h_holds
  rw [Operations.forAllNoOffset_append] at h_holds
  obtain ⟨h1, h2⟩ := h_holds
  have h1a := forAllNoOffset_constraints _ h1
    (by intro s hs; rw [mat_subcircuits] at hs; simp at hs)
  have h2a := forAllNoOffset_constraints _ h2
    (by intro s hs; rw [assertZeroLazy_subcircuits] at hs; simp at hs)
  have hi0 : Expression.eval env input_var[0] = input[0] := by rw [← h_input]; simp
  have hi1 : Expression.eval env input_var[1] = input[1] := by rw [← h_input]; simp
  have hmat : Expression.eval env ((mat (.mul input_var[0] input_var[0]) i₀).1)
      = Expression.eval env input_var[0] * Expression.eval env input_var[0] := by
    rw [mat_output_eq]
    exact matOut_eval env _ i₀ (by rwa [mat_operations_eq] at h1a)
  have hz := azl_eval env (Expression.mul input_var[1] input_var[1] -
    (Expression.mul input_var[0] ((mat (Expression.mul input_var[0] input_var[0]) i₀).1) +
      sc pa input_var[0] + cst pb)) _ h2a
  simp only [circuit_norm, hmat, sc, cst, hi0, hi1, pa, pb, StandardECDSA.params] at hz
  have hpa : params.a = pa := rfl
  have hpb : params.b = pb := rfl
  refine ⟨?_, ?_⟩
  · refine StandardECDSA.Math.AffineBridge.short_nonsingular params input[0] input[1] ?_
    rw [hpa, hpb]
    simp only [pa, pb]
    linear_combination hz
  · exact requirements_of_nil env _
      (by simp [isOnCurveMain, isOnCurve, mm, bind_snd, Operations.interactions_append,
        mat_interactions, assertZeroLazy_interactions])
      (by simp [isOnCurveMain, isOnCurve, mm, bind_snd, Operations.subcircuits_append,
        mat_subcircuits, assertZeroLazy_subcircuits])

/-! ## `pointEquality` as a `FormalAssertion` -/

/-- Semantic spec of `pointEquality`: the projective point `(x, y, z)` equals the
affine point `(px, py)`. -/
def pointEqualitySpec (i : fields 5 Fp) : Prop :=
  i[0] = i[2] * i[3] ∧ i[1] = i[2] * i[4]

theorem pointEqualityMain_soundness :
    FormalAssertion.Soundness Fp pointEqualityMain (fun _ => True) pointEqualitySpec := by
  circuit_proof_start
  simp only [pointEqualityMain, pointEquality, bind_snd] at h_holds
  rw [Operations.forAllNoOffset_append, Operations.forAllNoOffset_append] at h_holds
  obtain ⟨h1, h2, h3⟩ := h_holds
  have h1a := forAllNoOffset_constraints _ h1
    (by intro s hs; rw [mat_subcircuits] at hs; simp at hs)
  have h2a := forAllNoOffset_constraints _ h2
    (by intro s hs; rw [assertZeroLazy_subcircuits] at hs; simp at hs)
  have h3a := forAllNoOffset_constraints _ h3
    (by intro s hs; rw [assertZeroLazy_subcircuits] at hs; simp at hs)
  have hi0 : Expression.eval env input_var[0] = input[0] := by rw [← h_input]; simp
  have hi1 : Expression.eval env input_var[1] = input[1] := by rw [← h_input]; simp
  have hi2 : Expression.eval env input_var[2] = input[2] := by rw [← h_input]; simp
  have hi3 : Expression.eval env input_var[3] = input[3] := by rw [← h_input]; simp
  have hi4 : Expression.eval env input_var[4] = input[4] := by rw [← h_input]; simp
  have hmat : Expression.eval env ((mat input_var[2] i₀).1) = Expression.eval env input_var[2] := by
    rw [mat_output_eq]
    exact matOut_eval env _ i₀ (by rwa [mat_operations_eq] at h1a)
  have hz1 := azl_eval env (input_var[0] - Expression.mul ((mat input_var[2] i₀).1) input_var[3])
    _ h2a
  have hz2 := azl_eval env (input_var[1] - Expression.mul ((mat input_var[2] i₀).1) input_var[4])
    _ h3a
  simp only [circuit_norm, hmat, hi0, hi1, hi2, hi3, hi4] at hz1 hz2
  refine ⟨?_, ?_⟩
  · constructor
    · linear_combination hz1
    · linear_combination hz2
  · exact requirements_of_nil env _
      (by simp [pointEqualityMain, pointEquality, bind_snd, Operations.interactions_append,
        mat_interactions, assertZeroLazy_interactions])
      (by simp [pointEqualityMain, pointEquality, bind_snd, Operations.subcircuits_append,
        mat_subcircuits, assertZeroLazy_subcircuits])

/-! ## Completeness -/

theorem isOnCurveMain_completeness :
    FormalAssertion.Completeness Fp isOnCurveMain (fun _ => True) isOnCurveSpec := by
  circuit_proof_start
  simp only [isOnCurveSpec] at h_spec
  simp only [isOnCurveMain, isOnCurve, mm, bind_snd] at h_env ⊢
  rw [ulwc_append] at h_env
  obtain ⟨hA, hB⟩ := h_env
  simp only [ConstraintsHold.Completeness, Operations.forAllNoOffset_append]
  refine ⟨?_, ?_⟩
  · rw [mat_operations_eq] at hA ⊢
    exact mat_complete _ i₀ env hA
  · refine assertZeroLazy_complete _ _ env hB ?_
    have hi0 : Expression.eval env.toEnvironment input_var[0] = input[0] := by
      rw [← h_input]; simp
    have hi1 : Expression.eval env.toEnvironment input_var[1] = input[1] := by
      rw [← h_input]; simp
    have hxx : Expression.eval env.toEnvironment
        ((mat (.mul input_var[0] input_var[0]) i₀).1) = input[0] * input[0] := by
      rw [mat_output_eq]
      rw [matOut_eval_complete env (.mul input_var[0] input_var[0]) i₀
        (by rwa [mat_operations_eq] at hA)]
      simp only [Expression.eval, hi0]
    have hcurve : input[1] ^ 2 = input[0] ^ 3 + params.a * input[0] + params.b :=
      ns_equation input[0] input[1] h_spec
    have hpa : params.a = pa := rfl
    have hpb : params.b = pb := rfl
    simp only [circuit_norm, sc, cst, hi0, hi1, hxx, pa, pb]
    have hpa' : params.a = Challenge.Specs.ECDSAP256.params.a := rfl
    have hpb' : params.b = Challenge.Specs.ECDSAP256.params.b := rfl
    rw [← hpa', ← hpb']
    linear_combination hcurve

theorem pointEqualityMain_completeness :
    FormalAssertion.Completeness Fp pointEqualityMain (fun _ => True) pointEqualitySpec := by
  circuit_proof_start
  simp only [pointEqualitySpec] at h_spec
  obtain ⟨hspec1, hspec2⟩ := h_spec
  simp only [pointEqualityMain, pointEquality, bind_snd] at h_env ⊢
  rw [ulwc_append] at h_env
  obtain ⟨hA, h_env⟩ := h_env
  rw [ulwc_append] at h_env
  obtain ⟨hB, hC⟩ := h_env
  simp only [ConstraintsHold.Completeness, Operations.forAllNoOffset_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [mat_operations_eq] at hA ⊢
    exact mat_complete _ i₀ env hA
  · refine assertZeroLazy_complete _ _ env hB ?_
    have hi0 : Expression.eval env.toEnvironment input_var[0] = input[0] := by
      rw [← h_input]; simp
    have hi2 : Expression.eval env.toEnvironment input_var[2] = input[2] := by
      rw [← h_input]; simp
    have hi3 : Expression.eval env.toEnvironment input_var[3] = input[3] := by
      rw [← h_input]; simp
    have hz : Expression.eval env.toEnvironment ((mat input_var[2] i₀).1) = input[2] := by
      rw [mat_output_eq]
      rw [matOut_eval_complete env input_var[2] i₀ (by rwa [mat_operations_eq] at hA)]
      exact hi2
    simp only [circuit_norm, hi0, hi2, hi3, hz]
    linear_combination hspec1
  · refine assertZeroLazy_complete _ _ env hC ?_
    have hi1 : Expression.eval env.toEnvironment input_var[1] = input[1] := by
      rw [← h_input]; simp
    have hi2 : Expression.eval env.toEnvironment input_var[2] = input[2] := by
      rw [← h_input]; simp
    have hi4 : Expression.eval env.toEnvironment input_var[4] = input[4] := by
      rw [← h_input]; simp
    have hz : Expression.eval env.toEnvironment ((mat input_var[2] i₀).1) = input[2] := by
      rw [mat_output_eq]
      rw [matOut_eval_complete env input_var[2] i₀ (by rwa [mat_operations_eq] at hA)]
      exact hi2
    simp only [circuit_norm, hi1, hi2, hi4, hz]
    linear_combination hspec2

/-! ## Bundled `FormalAssertion`s -/

/-- `isOnCurve` bundled as a `FormalAssertion`: the assertion is exactly the
affine curve equation. -/
def isOnCurveAssertion : FormalAssertion Fp (fields 2) where
  main := isOnCurveMain
  Assumptions := fun _ => True
  Spec := isOnCurveSpec
  soundness := isOnCurveMain_soundness
  completeness := isOnCurveMain_completeness
  requirementsChannelsLawful := by
    intro input offset
    simp only [isOnCurveMain, isOnCurve, mm, bind_snd]
    exact requirementsChannelsLawful_of_nil
      (by intro s hs
          simp only [Operations.subcircuits_append, mat_subcircuits,
            assertZeroLazy_subcircuits, List.nil_append, List.not_mem_nil] at hs)
      (by simp [Operations.interactions_append, mat_interactions,
        assertZeroLazy_interactions])

/-- `pointEquality` bundled as a `FormalAssertion`: the projective point
`(x, y, z)` equals the affine point `(px, py)`. -/
def pointEqualityAssertion : FormalAssertion Fp (fields 5) where
  main := pointEqualityMain
  Assumptions := fun _ => True
  Spec := pointEqualitySpec
  soundness := pointEqualityMain_soundness
  completeness := pointEqualityMain_completeness
  requirementsChannelsLawful := by
    intro input offset
    simp only [pointEqualityMain, pointEquality, bind_snd]
    exact requirementsChannelsLawful_of_nil
      (by intro s hs
          simp only [Operations.subcircuits_append, mat_subcircuits,
            assertZeroLazy_subcircuits, List.nil_append, List.not_mem_nil] at hs)
      (by simp [Operations.interactions_append, mat_interactions,
        assertZeroLazy_interactions])

end StandardECDSA.Gadgets
