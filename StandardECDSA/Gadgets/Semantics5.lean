/-
# Semantic bundling of `mux4`

`mux4` is the variable four-way point mux used by the joint ladder.  Unlike
`muxConst4` its local length is not syntactically constant: each of the six
`sel` calls allocates `matLen` of an expression that mentions `matOut` of an
earlier `sel`.  The offset independence needed by
`ElaboratedCircuit.localLength_eq` therefore has to be proved, and it follows
from `VarEq` (`Gadgets/VarShape.lean`): `matOut e n` and `matOut e m` differ
only in variable indices, hence have the same `deg` and the same `matLen`.

Task T10 (semantic half).
-/

import StandardECDSA.Gadgets.Semantics4

namespace StandardECDSA.Gadgets

open WeierstrassCurve

/-! ## The six `sel` arguments of `mux4` -/

/-- First `sel` argument: x-coordinate of the `b0` mux. -/
def mux4A1 (b0 : E) (p0 p1 : Pt) : E := p0.1 + Expression.mul b0 (p1.1 - p0.1)

/-- Second `sel` argument: x-coordinate of the `b1` mux. -/
def mux4A2 (b0 : E) (p2 p3 : Pt) : E := p2.1 + Expression.mul b0 (p3.1 - p2.1)

/-- Third `sel` argument: x-coordinate of the final mux. -/
def mux4A3 (b1 : E) (a1 a2 : E) (n : ℕ) : E :=
  matOut a1 n + Expression.mul b1 (matOut a2 (n + matLen a1) - matOut a1 n)

/-- Fourth `sel` argument: y-coordinate of the `b0` mux. -/
def mux4A4 (b0 : E) (p0 p1 : Pt) : E := p0.2 + Expression.mul b0 (p1.2 - p0.2)

/-- Fifth `sel` argument: y-coordinate of the `b1` mux. -/
def mux4A5 (b0 : E) (p2 p3 : Pt) : E := p2.2 + Expression.mul b0 (p3.2 - p2.2)

/-- Sixth `sel` argument: y-coordinate of the final mux. -/
def mux4A6 (b1 : E) (a4 a5 : E) (off : ℕ) : E :=
  matOut a4 off + Expression.mul b1 (matOut a5 (off + matLen a4) - matOut a4 off)

/-- Offset of the y-coordinate block of `mux4`. -/
def mux4Off (b1 : E) (a1 a2 : E) (n : ℕ) : ℕ :=
  n + matLen a1 + matLen a2 + matLen (mux4A3 b1 a1 a2 n)

/-! ## Offset independence of the two offset-dependent arguments -/

theorem mux4A3_varEq (b1 a1 a2 : E) : ∀ n m, VarEq (mux4A3 b1 a1 a2 n) (mux4A3 b1 a1 a2 m) := by
  intro n m
  simp only [mux4A3]
  exact .add (matOut_varEq _ n m)
    (.mul (.refl _) (.sub (matOut_varEq _ _ _) (matOut_varEq _ n m)))

theorem mux4A3_matLen (b1 a1 a2 : E) (n : ℕ) :
    matLen (mux4A3 b1 a1 a2 n) = matLen (mux4A3 b1 a1 a2 0) :=
  (mux4A3_varEq b1 a1 a2 n 0).matLen_eq

theorem mux4A6_varEq (b1 a4 a5 : E) : ∀ n m, VarEq (mux4A6 b1 a4 a5 n) (mux4A6 b1 a4 a5 m) := by
  intro n m
  simp only [mux4A6]
  exact .add (matOut_varEq _ n m)
    (.mul (.refl _) (.sub (matOut_varEq _ _ _) (matOut_varEq _ n m)))

theorem mux4A6_matLen (b1 a4 a5 : E) (n : ℕ) :
    matLen (mux4A6 b1 a4 a5 n) = matLen (mux4A6 b1 a4 a5 0) :=
  (mux4A6_varEq b1 a4 a5 n 0).matLen_eq

/-! ## Offset-free local length -/

/-- Offset-free local length of `mux4`: the sum of the six `matLen`s of the
`sel` arguments, evaluated at offset `0`. -/
def mux4Len (b0 b1 : E) (p0 p1 p2 p3 : Pt) : ℕ :=
  matLen (mux4A1 b0 p0 p1) +
    (matLen (mux4A2 b0 p2 p3) +
      (matLen (mux4A3 b1 (mux4A1 b0 p0 p1) (mux4A2 b0 p2 p3) 0) +
        (matLen (mux4A4 b0 p0 p1) +
          (matLen (mux4A5 b0 p2 p3) +
            matLen (mux4A6 b1 (mux4A4 b0 p0 p1) (mux4A5 b0 p2 p3)
              (mux4Off b1 (mux4A1 b0 p0 p1) (mux4A2 b0 p2 p3) 0))))))

/-- The local length of `mux4` at any offset, in the named form. -/
theorem mux4_localLength (b0 b1 : E) (p0 p1 p2 p3 : Pt) (n : ℕ) :
    (mux4 b0 b1 p0 p1 p2 p3).localLength n =
      matLen (mux4A1 b0 p0 p1) +
        (matLen (mux4A2 b0 p2 p3) +
          (matLen (mux4A3 b1 (mux4A1 b0 p0 p1) (mux4A2 b0 p2 p3) n) +
            (matLen (mux4A4 b0 p0 p1) +
              (matLen (mux4A5 b0 p2 p3) +
                matLen (mux4A6 b1 (mux4A4 b0 p0 p1) (mux4A5 b0 p2 p3)
                  (mux4Off b1 (mux4A1 b0 p0 p1) (mux4A2 b0 p2 p3) n)))))) := by
  simp only [mux4, sel, circuit_norm, Circuit.localLength, bind_snd, pure_snd,
    Operations.append_localLength, List.append_nil, Nat.zero_add, mat_localLength_eq,
    mat_output_eq, mux4A1, mux4A2, mux4A3, mux4A4, mux4A5, mux4A6, mux4Off]

theorem mux4Len_eq (b0 b1 : E) (p0 p1 p2 p3 : Pt) (n : ℕ) :
    (mux4 b0 b1 p0 p1 p2 p3).localLength n = mux4Len b0 b1 p0 p1 p2 p3 := by
  rw [mux4_localLength, mux4Len, mux4A3_matLen,
    (mux4A6_varEq b1 (mux4A4 b0 p0 p1) (mux4A5 b0 p2 p3)
      (mux4Off b1 (mux4A1 b0 p0 p1) (mux4A2 b0 p2 p3) n)
      (mux4Off b1 (mux4A1 b0 p0 p1) (mux4A2 b0 p2 p3) 0)).matLen_eq]

/-! ## The `ExplicitCircuit` and `ElaboratedCircuit` instances -/

/-- Output of `mux4` at offset `n`, in the named form. -/
def mux4Out (b0 b1 : E) (p0 p1 p2 p3 : Pt) (n : ℕ) : Pt :=
  (matOut (mux4A3 b1 (mux4A1 b0 p0 p1) (mux4A2 b0 p2 p3) n)
      (n + matLen (mux4A1 b0 p0 p1) + matLen (mux4A2 b0 p2 p3)),
   matOut (mux4A6 b1 (mux4A4 b0 p0 p1) (mux4A5 b0 p2 p3)
      (mux4Off b1 (mux4A1 b0 p0 p1) (mux4A2 b0 p2 p3) n))
      (mux4Off b1 (mux4A1 b0 p0 p1) (mux4A2 b0 p2 p3) n
        + matLen (mux4A4 b0 p0 p1) + matLen (mux4A5 b0 p2 p3)))

theorem mux4_output (b0 b1 : E) (p0 p1 p2 p3 : Pt) (n : ℕ) :
    (mux4 b0 b1 p0 p1 p2 p3 n).1 = mux4Out b0 b1 p0 p1 p2 p3 n := by
  simp only [mux4, sel, circuit_norm, bind_fst, pure_fst,
    Operations.append_localLength, List.append_nil, Nat.zero_add, mat_localLength_eq,
    mat_output_eq, mux4Out, mux4A1, mux4A2, mux4A3, mux4A4, mux4A5, mux4A6, mux4Off]

/-- The `do`-block structure of `mux4`, as a composition of `mat` circuits.
Used only to inherit `subcircuitsConsistent` and `channelsLawful`. -/
def mux4OpsExplicit (b0 b1 : E) (p0 p1 p2 p3 : Pt) :
    ExplicitCircuit (mux4 b0 b1 p0 p1 p2 p3) :=
  ExplicitCircuit.from_bind (matExplicit (mux4A1 b0 p0 p1)) fun ax =>
  ExplicitCircuit.from_bind (matExplicit (mux4A2 b0 p2 p3)) fun bx =>
  ExplicitCircuit.from_bind (matExplicit (ax + Expression.mul b1 (bx - ax))) fun x =>
  ExplicitCircuit.from_bind (matExplicit (mux4A4 b0 p0 p1)) fun ay =>
  ExplicitCircuit.from_bind (matExplicit (mux4A5 b0 p2 p3)) fun by' =>
  ExplicitCircuit.from_bind (matExplicit (ay + Expression.mul b1 (by' - ay))) fun y =>
  ExplicitCircuit.from_pure (a := (x, y))

/-- `mux4` as an `ExplicitCircuit` with an offset-free local length. -/
def mux4Explicit (b0 b1 : E) (p0 p1 p2 p3 : Pt) :
    ExplicitCircuit (mux4 b0 b1 p0 p1 p2 p3) where
  output := mux4Out b0 b1 p0 p1 p2 p3
  localLength := fun _ => mux4Len b0 b1 p0 p1 p2 p3
  localLength_eq := mux4Len_eq b0 b1 p0 p1 p2 p3
  operations := fun n => (mux4 b0 b1 p0 p1 p2 p3 n).2
  output_eq := mux4_output b0 b1 p0 p1 p2 p3
  subcircuitsConsistent := (mux4OpsExplicit b0 b1 p0 p1 p2 p3).subcircuitsConsistent
  channelsWithGuarantees := fun _ => []
  channelsLawful := (mux4OpsExplicit b0 b1 p0 p1 p2 p3).channelsLawful

/-! ## `mux4` with the ten field inputs -/

/-- Input layout: `b0, b1, p0x, p0y, p1x, p1y, p2x, p2y, p3x, p3y`. -/
def mux4Main (i : Var (fields 10) Fp) : Circuit Fp (Var (ProvablePair field field) Fp) :=
  mux4 i[0] i[1] (i[2], i[3]) (i[4], i[5]) (i[6], i[7]) (i[8], i[9])

def mux4Family :
    ExplicitCircuits (fun i : Var (fields 10) Fp =>
      mux4 i[0] i[1] (i[2], i[3]) (i[4], i[5]) (i[6], i[7]) (i[8], i[9])) :=
  ExplicitCircuits.fromSingle (fun i =>
    mux4Explicit i[0] i[1] (i[2], i[3]) (i[4], i[5]) (i[6], i[7]) (i[8], i[9]))

instance : ExplicitCircuits.IsElaborated
    (fun i : Var (fields 10) Fp =>
      mux4 i[0] i[1] (i[2], i[3]) (i[4], i[5]) (i[6], i[7]) (i[8], i[9])) mux4Family where
  localLength_eq := by intros; rfl
  channelsWithGuarantees_eq := by intros; rfl

instance : ElaboratedCircuit Fp (fields 10) (ProvablePair field field) mux4Main :=
  ElaboratedCircuit.fromExplicit mux4Family
    (inferInstance : ExplicitCircuits.IsElaborated
      (fun i : Var (fields 10) Fp =>
        mux4 i[0] i[1] (i[2], i[3]) (i[4], i[5]) (i[6], i[7]) (i[8], i[9])) mux4Family)

/-! ## Semantic spec of `mux4` -/

/-- Semantic spec of `mux4`: the output is entry `b0 + 2*b1` of the four input
points, i.e. `p0` for `(0,0)`, `p1` for `(1,0)`, `p2` for `(0,1)` and `p3` for
`(1,1)`. -/
def mux4Spec (i : fields 10 Fp) (out : Fp × Fp) : Prop :=
  ∃ c0 c1 : Bool, i[0] = c0.toNat ∧ i[1] = c1.toNat ∧
    out = (if c0 then (if c1 then (i[8], i[9]) else (i[4], i[5]))
           else (if c1 then (i[6], i[7]) else (i[2], i[3])))

/-! ## Evaluation of the six `sel` arguments -/

theorem mux4A1_eval (env : Environment Fp) (b0 : E) (p0 p1 : Pt) :
    env (mux4A1 b0 p0 p1) = env p0.1 + env b0 * (env p1.1 - env p0.1) := by
  simp only [mux4A1, circuit_norm]

theorem mux4A2_eval (env : Environment Fp) (b0 : E) (p2 p3 : Pt) :
    env (mux4A2 b0 p2 p3) = env p2.1 + env b0 * (env p3.1 - env p2.1) := by
  simp only [mux4A2, circuit_norm]

theorem mux4A3_eval (env : Environment Fp) (b1 a1 a2 : E) (n : ℕ) :
    env (mux4A3 b1 a1 a2 n) =
      env (matOut a1 n) + env b1 * (env (matOut a2 (n + matLen a1)) - env (matOut a1 n)) := by
  simp only [mux4A3, circuit_norm]

theorem mux4A4_eval (env : Environment Fp) (b0 : E) (p0 p1 : Pt) :
    env (mux4A4 b0 p0 p1) = env p0.2 + env b0 * (env p1.2 - env p0.2) := by
  simp only [mux4A4, circuit_norm]

theorem mux4A5_eval (env : Environment Fp) (b0 : E) (p2 p3 : Pt) :
    env (mux4A5 b0 p2 p3) = env p2.2 + env b0 * (env p3.2 - env p2.2) := by
  simp only [mux4A5, circuit_norm]

theorem mux4A6_eval (env : Environment Fp) (b1 a4 a5 : E) (off : ℕ) :
    env (mux4A6 b1 a4 a5 off) =
      env (matOut a4 off) + env b1 * (env (matOut a5 (off + matLen a4)) - env (matOut a4 off)) := by
  simp only [mux4A6, circuit_norm]

theorem mux4Main_output (i : Var (fields 10) Fp) (n : ℕ) :
    ElaboratedCircuit.output mux4Main i n =
      mux4Out i[0] i[1] (i[2], i[3]) (i[4], i[5]) (i[6], i[7]) (i[8], i[9]) n := rfl

/-! ## Soundness -/

theorem mux4Main_soundness :
    Soundness Fp mux4Main (fun i => (i[0] = 0 ∨ i[0] = 1) ∧ (i[1] = 0 ∨ i[1] = 1))
      mux4Spec := by
  circuit_proof_start
  obtain ⟨hb0, hb1⟩ := h_assumptions
  obtain ⟨c0, hc0⟩ := exists_bool_of_bit hb0
  obtain ⟨c1, hc1⟩ := exists_bool_of_bit hb1
  have hi0 : Expression.eval env input_var[0] = input[0] := by rw [← h_input]; simp
  have hi1 : Expression.eval env input_var[1] = input[1] := by rw [← h_input]; simp
  have hi2 : Expression.eval env input_var[2] = input[2] := by rw [← h_input]; simp
  have hi3 : Expression.eval env input_var[3] = input[3] := by rw [← h_input]; simp
  have hi4 : Expression.eval env input_var[4] = input[4] := by rw [← h_input]; simp
  have hi5 : Expression.eval env input_var[5] = input[5] := by rw [← h_input]; simp
  have hi6 : Expression.eval env input_var[6] = input[6] := by rw [← h_input]; simp
  have hi7 : Expression.eval env input_var[7] = input[7] := by rw [← h_input]; simp
  have hi8 : Expression.eval env input_var[8] = input[8] := by rw [← h_input]; simp
  have hi9 : Expression.eval env input_var[9] = input[9] := by rw [← h_input]; simp
  have hh := h_holds
  simp only [mux4Main, mux4, sel, bind_snd, pure_snd, Operations.localLength,
    Operations.append_localLength, List.nil_append, List.append_nil, Nat.add_zero,
    Nat.zero_add, mat_localLength_eq, mat_output_eq,
    Operations.forAllNoOffset_append] at hh
  obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6⟩ := hh
  have e1 := mat_eval_gen _ i₀ env _ (fun _ hx => hx) ha1
  have e2 := mat_eval_gen _ _ env _ (fun _ hx => hx) ha2
  have e3 := mat_eval_gen _ _ env _ (fun _ hx => hx) ha3
  have e4 := mat_eval_gen _ _ env _ (fun _ hx => hx) ha4
  have e5 := mat_eval_gen _ _ env _ (fun _ hx => hx) ha5
  have e6 := mat_eval_gen _ _ env _ (fun _ hx => hx) ha6
  refine ⟨⟨c0, c1, hc0, hc1, ?_⟩, ?_⟩
  · rw [mux4Main_output]
    simp only [mux4Out, mux4A1, mux4A2, mux4A3, mux4A4, mux4A5, mux4A6, mux4Off]
    rw [e3, e6]
    simp only [circuit_norm]
    rw [e1, e2, e4, e5]
    simp only [circuit_norm]
    simp only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9]
    rw [hc0, hc1]
    cases c0 <;> cases c1 <;> simp
  · simp only [mux4Main, mux4, sel, circuit_norm, bind_snd, pure_snd,
      Operations.localLength, Operations.append_localLength, List.nil_append,
      List.append_nil, Nat.add_zero, Nat.zero_add, mat_localLength_eq, mat_output_eq,
      Operations.forAllNoOffset_append]
    exact ⟨mat_requirements _ i₀ env, mat_requirements _ _ env, mat_requirements _ _ env,
      mat_requirements _ _ env, mat_requirements _ _ env, mat_requirements _ _ env⟩

/-! ## Completeness -/

/-- `mat_complete` stated on `(mat e n).2` rather than `matOps e n`. -/
theorem mat_complete' (e : E) (n : ℕ) (env : ProverEnvironment Fp)
    (h : env.UsesLocalWitnessesCompleteness n ((mat e) n).2) :
    ConstraintsHold.Completeness env ((mat e) n).2 := by
  rw [mat_operations_eq] at h ⊢
  exact mat_complete e n env h

theorem mux4Main_completeness :
    Completeness Fp mux4Main (fun i => (i[0] = 0 ∨ i[0] = 1) ∧ (i[1] = 0 ∨ i[1] = 1)) := by
  circuit_proof_start
  simp only [mux4Main, mux4, sel, bind_snd, pure_snd, Operations.localLength,
    Operations.append_localLength, List.nil_append, List.append_nil, Nat.add_zero,
    Nat.zero_add, mat_localLength_eq, mat_output_eq] at h_env ⊢
  simp only [ulwc_append, mat_localLength_eq] at h_env
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h_env
  simp only [ConstraintsHold.Completeness, Operations.forAllNoOffset_append]
  exact ⟨mat_complete' _ i₀ env h1, mat_complete' _ _ env h2, mat_complete' _ _ env h3,
    mat_complete' _ _ env h4, mat_complete' _ _ env h5, mat_complete' _ _ env h6⟩

/-- `RequirementsChannelsLawful` composes over `++` when both channel lists are empty. -/
theorem requirementsChannelsLawful_append {a b : Operations Fp}
    (h1 : Operations.RequirementsChannelsLawful a [] [])
    (h2 : Operations.RequirementsChannelsLawful b [] []) :
    Operations.RequirementsChannelsLawful (a ++ b) [] [] := by
  obtain ⟨s1, c1, i1⟩ := h1
  obtain ⟨s2, c2, i2⟩ := h2
  refine ⟨?_, ?_, ?_⟩
  · rw [Operations.subcircuitChannelsWithRequirements_append]
    have e1 : Operations.subcircuitChannelsWithRequirements a = [] := List.subset_nil.mp s1
    have e2 : Operations.subcircuitChannelsWithRequirements b = [] := List.subset_nil.mp s2
    rw [e1, e2]
    simp
  · rw [Operations.shallowChannels_append]
    intro c hc
    rw [List.mem_append] at hc
    exact hc.elim (c1 c) (c2 c)
  · intro env h
    rw [ConstraintsHold.Shallow, Operations.forAllNoOffset_append] at h
    rw [Operations.InChannelsOrRequirements, Operations.forAllNoOffset_append]
    exact ⟨i1 env h.1, i2 env h.2⟩

def mux4Circuit : FormalCircuit Fp (fields 10) (ProvablePair field field) where
  main := mux4Main
  Assumptions := fun i => (i[0] = 0 ∨ i[0] = 1) ∧ (i[1] = 0 ∨ i[1] = 1)
  Spec := mux4Spec
  soundness := mux4Main_soundness
  completeness := mux4Main_completeness
  requirementsChannelsLawful := by
    intro input offset
    simp only [mux4Main, mux4, sel, bind_snd, pure_snd, Operations.localLength,
      Operations.append_localLength, List.nil_append, List.append_nil, Nat.add_zero,
      Nat.zero_add, mat_localLength_eq, mat_output_eq]
    exact requirementsChannelsLawful_append
      (mat_requirementsChannelsLawful _ offset)
      (requirementsChannelsLawful_append
        (mat_requirementsChannelsLawful _ _)
        (requirementsChannelsLawful_append
          (mat_requirementsChannelsLawful _ _)
          (requirementsChannelsLawful_append
            (mat_requirementsChannelsLawful _ _)
            (requirementsChannelsLawful_append
              (mat_requirementsChannelsLawful _ _)
              (mat_requirementsChannelsLawful _ _)))))

end StandardECDSA.Gadgets
