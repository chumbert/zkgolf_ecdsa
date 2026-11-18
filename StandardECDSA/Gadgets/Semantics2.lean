/-
# Bundled semantic specs for the `mat`-based gadgets

Each gadget is exposed as a Clean `FormalCircuit` whose `Spec` is a *semantic*
statement (selection / group law), not a list of rows.  Soundness is proved from
an arbitrary satisfying assignment via `mat_eval_gen`; completeness from the
honest witness generator.

Task T05 / T10 (semantic half).
-/

import StandardECDSA.Gadgets.MatSemantics
import StandardECDSA.Gadgets.IteExplicit
import StandardECDSA.Gadgets.Select
import StandardECDSA.Gadgets.Affine
import StandardECDSA.Gadgets.ELM
import StandardECDSA.Gadgets.Lemmas
import Clean.Circuit.Formal

namespace StandardECDSA.Gadgets

/-! ## Trivial-condition lemmas for `matOps`

`matOps e n` is stuck for opaque `e`, so `forAllNoOffset` cannot reduce.  The
requirements conjuncts of `Soundness` and of `FormalCircuitBase` need exactly
this for conditions whose `witness`/`assert` components are `True`. -/

theorem matOps_forAllNoOffset (e : E) : ∀ n (c : ConditionNoOffset Fp),
    (∀ (m : ℕ) (ir : WitgenIR Fp m), c.witness m ir) →
    (∀ x, c.assert x) →
    Operations.forAllNoOffset c (matOps e n) := by
  induction e with
  | var v => intro n c _ _; trivial
  | const k => intro n c _ _; trivial
  | add a b iha ihb =>
      intro n c hw ha
      rw [matOps, Operations.forAllNoOffset_append]
      exact ⟨iha n c hw ha, ihb _ c hw ha⟩
  | mul a b iha ihb =>
      intro n c hw ha
      rw [matOps, Operations.forAllNoOffset_append]
      refine ⟨iha n c hw ha, ?_⟩
      rw [Operations.forAllNoOffset_append]
      refine ⟨ihb _ c hw ha, ?_⟩
      split
      · trivial
      · simp only [Operations.forAllNoOffset]
        exact ⟨hw _ _, ha _, trivial⟩

/-- The requirements conjunct of `Soundness` for a `mat`-based circuit. -/
theorem mat_requirements (e : E) (n : ℕ) (env : Environment Fp) :
    Operations.forAllNoOffset
      { interact := fun i => i.Requirements env
        subcircuit := fun s => s.channelsWithRequirements = [] ∨ s.Assumptions env }
      ((mat e) n).2 := by
  rw [mat_operations_eq]
  exact matOps_forAllNoOffset e n _ (fun _ _ => trivial) (fun _ => trivial)

/-- `RequirementsChannelsLawful` for a `mat`-based circuit with no channels. -/
theorem matOps_requirementsChannelsLawful (e : E) : ∀ n,
    Operations.RequirementsChannelsLawful (matOps e n) [] [] := by
  induction e with
  | var v =>
      intro n
      exact ⟨by simp [matOps, Operations.subcircuitChannelsWithRequirements],
        by simp [matOps, Operations.shallowChannels],
        fun env _ => matOps_forAllNoOffset _ n _ (fun _ _ => trivial) (fun _ => trivial)⟩
  | const k =>
      intro n
      exact ⟨by simp [matOps, Operations.subcircuitChannelsWithRequirements],
        by simp [matOps, Operations.shallowChannels],
        fun env _ => matOps_forAllNoOffset _ n _ (fun _ _ => trivial) (fun _ => trivial)⟩
  | add a b iha ihb =>
      intro n
      rw [matOps]
      refine ⟨?_, ?_, ?_⟩
      · rw [Operations.subcircuitChannelsWithRequirements_append]
        have h1 := List.subset_nil.mp (iha n).1
        have h2 := List.subset_nil.mp (ihb (n + matLen a)).1
        rw [h1, h2]
        simp
      · rw [Operations.shallowChannels_append]
        intro c hc
        rw [List.mem_append] at hc
        exact hc.elim ((iha n).2.1 c) ((ihb (n + matLen a)).2.1 c)
      · intro env _
        rw [Operations.InChannelsOrRequirements, Operations.forAllNoOffset_append]
        exact ⟨matOps_forAllNoOffset a n _ (fun _ _ => trivial) (fun _ => trivial),
          matOps_forAllNoOffset b (n + matLen a) _ (fun _ _ => trivial) (fun _ => trivial)⟩
  | mul a b iha ihb =>
      intro n
      rw [matOps]
      refine ⟨?_, ?_, ?_⟩
      · rw [Operations.subcircuitChannelsWithRequirements_append]
        have h1 := List.subset_nil.mp (iha n).1
        rw [h1]
        rw [Operations.subcircuitChannelsWithRequirements_append]
        have h2 := List.subset_nil.mp (ihb (n + matLen a)).1
        rw [h2]
        split <;> simp [Operations.subcircuitChannelsWithRequirements]
      · rw [Operations.shallowChannels_append]
        intro c hc
        rw [List.mem_append] at hc
        refine hc.elim ((iha n).2.1 c) ?_
        intro hc'
        rw [Operations.shallowChannels_append] at hc'
        rw [List.mem_append] at hc'
        refine hc'.elim ((ihb (n + matLen a)).2.1 c) ?_
        intro hc''
        split at hc'' <;> simp_all [Operations.shallowChannels]
      · intro env _
        rw [Operations.InChannelsOrRequirements, Operations.forAllNoOffset_append]
        refine ⟨matOps_forAllNoOffset a n _ (fun _ _ => trivial) (fun _ => trivial), ?_⟩
        rw [Operations.forAllNoOffset_append]
        refine ⟨matOps_forAllNoOffset b (n + matLen a) _ (fun _ _ => trivial) (fun _ => trivial), ?_⟩
        split <;> trivial

/-- `RequirementsChannelsLawful` for a `mat`-based circuit. -/
theorem mat_requirementsChannelsLawful (e : E) (n : ℕ) :
    Operations.RequirementsChannelsLawful ((mat e) n).2 [] [] := by
  rw [mat_operations_eq]
  exact matOps_requirementsChannelsLawful e n

/-! ## Completeness of `mat`

`matOps e n` is stuck for opaque `e`, so neither `UsesLocalWitnessesCompleteness`
nor `ConstraintsHold.Completeness` can be unfolded by `simp`.  We prove the
implication by induction over the expression tree, mirroring
`matOps_forAllNoOffset`. -/

theorem ulwc_append (env : ProverEnvironment Fp) (n : ℕ) (as : Operations Fp) :
    ∀ bs : Operations Fp,
      env.UsesLocalWitnessesCompleteness n (as ++ bs) ↔
        env.UsesLocalWitnessesCompleteness n as ∧
          env.UsesLocalWitnessesCompleteness (n + as.localLength) bs := by
  induction as generalizing n with
  | nil => intro bs; simp [ProverEnvironment.UsesLocalWitnessesCompleteness,
      Operations.localLength]
  | cons op ops ih =>
      intro bs
      cases op with
      | witness m c =>
          simp only [List.cons_append, ProverEnvironment.UsesLocalWitnessesCompleteness,
            Operations.localLength, ih (n + m), Nat.add_assoc]
          tauto
      | assert e =>
          simp only [List.cons_append, ProverEnvironment.UsesLocalWitnessesCompleteness,
            Operations.localLength, ih n]
      | lookup l =>
          simp only [List.cons_append, ProverEnvironment.UsesLocalWitnessesCompleteness,
            Operations.localLength, ih n]
      | interact i =>
          simp only [List.cons_append, ProverEnvironment.UsesLocalWitnessesCompleteness,
            Operations.localLength, ih n]
      | subcircuit s =>
          simp only [List.cons_append, ProverEnvironment.UsesLocalWitnessesCompleteness,
            Operations.localLength, ih (n + s.localLength), Nat.add_assoc]
          tauto

/-- The `assert` row emitted by `mat` for a non-constant product is satisfied by
the honest witness generator. -/
theorem mat_assert_eval (a b : E) (n : ℕ) (env : ProverEnvironment Fp)
    (hw : env.ExtendsVector
      ((Witgen.WitgenIR.ofFExpr
        (.mul (.expr (matOut a n)) (.expr (matOut b (n + matLen a))))).eval env)
      (n + matLen a + matLen b)) :
    env (matOut a n * matOut b (n + matLen a) - .var ⟨n + matLen a + matLen b⟩) = 0 := by
  have h0 := hw ⟨0, by simp⟩
  rw [Witgen.WitgenIR.getElem_eval_ofFExpr] at h0
  simp only [Witgen.FExpr.eval] at h0
  show Expression.eval env.toEnvironment
    (matOut a n * matOut b (n + matLen a) - .var ⟨n + matLen a + matLen b⟩) = 0
  simp only [circuit_norm] at h0 ⊢
  rw [h0]
  ring

theorem mat_complete (e : E) : ∀ n (env : ProverEnvironment Fp),
    env.UsesLocalWitnessesCompleteness n (matOps e n) →
    ConstraintsHold.Completeness env (matOps e n) := by
  induction e with
  | var v =>
      intro n env _
      rw [matOps]
      simp [ConstraintsHold.Completeness, Operations.forAllNoOffset]
  | const k =>
      intro n env _
      rw [matOps]
      simp [ConstraintsHold.Completeness, Operations.forAllNoOffset]
  | add a b iha ihb =>
      intro n env h
      rw [matOps, ulwc_append] at h
      rw [matOps_localLength] at h
      rw [matOps, ConstraintsHold.Completeness, Operations.forAllNoOffset_append]
      exact ⟨iha n env h.1, ihb (n + matLen a) env h.2⟩
  | mul a b iha ihb =>
      intro n env h
      by_cases hc : deg a = 0 ∨ deg b = 0
      · simp only [matOps, hc, if_true, List.append_nil] at h ⊢
        rw [ulwc_append] at h
        rw [matOps_localLength] at h
        rw [ConstraintsHold.Completeness, Operations.forAllNoOffset_append]
        exact ⟨iha n env h.1, ihb (n + matLen a) env h.2⟩
      · simp only [matOps, hc, if_false] at h ⊢
        rw [ulwc_append] at h
        rw [matOps_localLength] at h
        obtain ⟨h1, h2⟩ := h
        rw [ulwc_append] at h2
        rw [matOps_localLength] at h2
        obtain ⟨h2a, h2b⟩ := h2
        rw [ConstraintsHold.Completeness, Operations.forAllNoOffset_append]
        refine ⟨iha n env h1, ?_⟩
        rw [Operations.forAllNoOffset_append]
        refine ⟨ihb (n + matLen a) env h2a, ?_⟩
        simp only [Operations.forAllNoOffset, ProverEnvironment.UsesLocalWitnessesCompleteness]
          at h2b ⊢
        exact ⟨trivial, mat_assert_eval a b n env h2b.1, trivial⟩

/-! ## `sel` -/

def selMain (i : Var (fields 3) Fp) : Circuit Fp (Var field Fp) := sel i[0] i[1] i[2]

instance : ElaboratedCircuit Fp (fields 3) field selMain := by
  unfold selMain sel
  elaborate_circuit

/-- Semantic spec of `sel`: the output is `x0` when `b = 0` and `x1` when
`b = 1`, written as the affine interpolation `x0 + b·(x1 - x0)`. -/
def selSpec (i : fields 3 Fp) (out : Fp) : Prop := out = i[1] + i[0] * (i[2] - i[1])

theorem selMain_soundness :
    Soundness Fp selMain (fun _ => True) selSpec := by
  circuit_proof_start
  refine ⟨?_, ?_⟩
  · have h := mat_eval_gen (input_var[1] + input_var[0] * (input_var[2] - input_var[1])) i₀ env
      { assert := fun e => Expression.eval env e = 0
        lookup := fun l => l.Soundness env
        interact := fun i => i.Guarantees env
        subcircuit := fun s => s.Assumptions env → s.Spec env } (fun _ hx => hx) h_holds
    simp only [selMain, sel, circuit_norm] at h
    show Expression.eval env (matOut (input_var[1] + input_var[0] * (input_var[2] - input_var[1])) i₀)
      = input[1] + input[0] * (input[2] - input[1])
    rw [h, ← h_input]
    simp
  · simp only [selMain, sel]
    exact mat_requirements _ i₀ env

theorem selMain_completeness :
    Completeness Fp selMain (fun _ => True) := by
  circuit_proof_start
  simp only [selMain, sel, circuit_norm] at h_env ⊢
  rw [mat_operations_eq] at h_env ⊢
  exact mat_complete _ i₀ env h_env

def selCircuit : FormalCircuit Fp (fields 3) field where
  main := selMain
  Assumptions := fun _ => True
  Spec := selSpec
  soundness := selMain_soundness
  completeness := selMain_completeness
  requirementsChannelsLawful := by
    intro input offset
    simp only [selMain, sel]
    exact mat_requirementsChannelsLawful _ offset

def muxConst4Main (tab : Array (Fp × Fp)) (i : Var (fields 2) Fp) :
    Circuit Fp (Var (ProvablePair field field) Fp) :=
  muxConst4 i[0] i[1] tab

instance (tab : Array (Fp × Fp)) :
    ElaboratedCircuit Fp (fields 2) (ProvablePair field field) (muxConst4Main tab) := by
  unfold muxConst4Main muxConst4
  elaborate_circuit

theorem muxConst4Main_output (tab : Array (Fp × Fp)) (i : Var (fields 2) Fp) (n : ℕ) :
    ElaboratedCircuit.output (muxConst4Main tab) i n =
      (muxConst4Coord (tab.getD 0 (0,0)).1 (tab.getD 1 (0,0)).1 (tab.getD 2 (0,0)).1 (tab.getD 3 (0,0)).1
          i[0] i[1] (matOut (i[0] * i[1]) n),
       muxConst4Coord (tab.getD 0 (0,0)).2 (tab.getD 1 (0,0)).2 (tab.getD 2 (0,0)).2 (tab.getD 3 (0,0)).2
          i[0] i[1] (matOut (i[0] * i[1]) n)) := rfl

/-- `eval_mul` with the `*` surface syntax (the `Mul` instance is definitionally but
not syntactically `Expression.mul`, so `simp` needs this spelling). -/
theorem eval_mul' (env : Environment Fp) (a b : E) :
    Expression.eval env (a * b) = Expression.eval env a * Expression.eval env b := by
  show Expression.eval env (Expression.mul a b) = _
  rw [eval_mul]

theorem muxConst4Coord_eval (v0 v1 v2 v3 : Fp) (b0 b1 b01 : E) (env : Environment Fp) :
    Expression.eval env (muxConst4Coord v0 v1 v2 v3 b0 b1 b01) =
      v0 + (v1 - v0) * Expression.eval env b0 + (v2 - v0) * Expression.eval env b1
        + (v3 - v2 - v1 + v0) * Expression.eval env b01 := by
  simp [muxConst4Coord, cst, sc, Expression.eval]

def muxConst4Spec (tab : Array (Fp × Fp)) (i : fields 2 Fp) (out : Fp × Fp) : Prop :=
  ∃ c0 c1 : Bool, i[0] = c0.toNat ∧ i[1] = c1.toNat ∧
    out = tab.getD (c0.toNat + 2 * c1.toNat) (0, 0)

theorem muxConst4Main_soundness (tab : Array (Fp × Fp)) :
    Soundness Fp (muxConst4Main tab)
      (fun i => (i[0] = 0 ∨ i[0] = 1) ∧ (i[1] = 0 ∨ i[1] = 1))
      (muxConst4Spec tab) := by
  circuit_proof_start
  obtain ⟨h0, h1⟩ := h_assumptions
  obtain ⟨c0, hc0⟩ := exists_bool_of_bit h0
  obtain ⟨c1, hc1⟩ := exists_bool_of_bit h1
  have hi0 : Expression.eval env input_var[0] = input[0] := by
    rw [← h_input]; simp
  have hi1 : Expression.eval env input_var[1] = input[1] := by
    rw [← h_input]; simp
  refine ⟨⟨c0, c1, hc0, hc1, ?_⟩, ?_⟩
  · have hh : Operations.forAllNoOffset
        { assert := fun e => Expression.eval env e = 0
          lookup := fun l => l.Soundness env
          interact := fun i => i.Guarantees env
          subcircuit := fun s => s.Assumptions env → s.Spec env }
        ((mat (Expression.mul input_var[0] input_var[1]) i₀)).2 := by
      simpa only [muxConst4Main, muxConst4, mm, bind_snd, pure_snd, List.append_nil] using h_holds
    have hw := mat_eval_gen (input_var[0] * input_var[1]) i₀ env
      { assert := fun e => Expression.eval env e = 0
        lookup := fun l => l.Soundness env
        interact := fun i => i.Guarantees env
        subcircuit := fun s => s.Assumptions env → s.Spec env } (fun _ hx => hx) hh
    rw [muxConst4Main_output]
    simp only [muxConst4Coord_eval]
    rw [hw]
    simp only [eval_mul', hi0, hi1, hc0, hc1]
    cases c0 <;> cases c1 <;> simp [muxConst4_spec] <;> (try constructor) <;> ring
  · simp only [muxConst4Main, muxConst4, mm, bind_snd, pure_snd, List.append_nil]
    exact mat_requirements _ i₀ env

theorem muxConst4Main_completeness (tab : Array (Fp × Fp)) :
    Completeness Fp (muxConst4Main tab)
      (fun i => (i[0] = 0 ∨ i[0] = 1) ∧ (i[1] = 0 ∨ i[1] = 1)) := by
  circuit_proof_start
  simp only [muxConst4Main, muxConst4, mm, circuit_norm, bind_snd, pure_snd,
    List.append_nil] at h_env ⊢
  rw [mat_operations_eq] at h_env ⊢
  exact mat_complete _ i₀ env h_env

def muxConst4Circuit (tab : Array (Fp × Fp)) :
    FormalCircuit Fp (fields 2) (ProvablePair field field) where
  main := muxConst4Main tab
  Assumptions := fun i => (i[0] = 0 ∨ i[0] = 1) ∧ (i[1] = 0 ∨ i[1] = 1)
  Spec := muxConst4Spec tab
  soundness := muxConst4Main_soundness tab
  completeness := muxConst4Main_completeness tab
  requirementsChannelsLawful := by
    intro input offset
    simp only [muxConst4Main, muxConst4, mm, bind_snd, pure_snd, List.append_nil]
    exact mat_requirementsChannelsLawful _ offset

end StandardECDSA.Gadgets
