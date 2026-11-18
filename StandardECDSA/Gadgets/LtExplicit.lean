/-
# `ExplicitCircuit` and `FormalAssertion` bundling for the comparators

`ltLoop` allocates one wire and emits one row per maximal zero run of the
bound.  This module

* proves the offset-free local length `ltLoopLen`,
* discharges `SubcircuitsConsistent`, `ChannelsLawful` and
  `RequirementsChannelsLawful`,
* bundles `assertLtOrderOf` and `assertLtOrderGuardedOf` as `FormalAssertion`s
  whose `Spec` is the arithmetic statement `prefVal x 256 ≤ bound`.

Task T06 / T07.
-/

import StandardECDSA.Gadgets.Semantics6
import StandardECDSA.Gadgets.Semantics4
import StandardECDSA.Gadgets.AzlExplicit
import StandardECDSA.Gadgets.Cost
import StandardECDSA.Gadgets.R1CS
import StandardECDSA.Gadgets.LocalLength

set_option maxRecDepth 100000

namespace StandardECDSA.Gadgets

open StandardECDSA.Math
open Challenge.Instances.ECDSA_P256_Digest.Interface

/-! ## Offset-free local length -/

/-- Number of wires allocated by `ltLoop`: one per zero run. -/
def ltLoopLen : List (Nat × Nat × Bool) → Nat
  | [] => 0
  | (_, _, bit) :: rest => (if bit then 0 else 1) + ltLoopLen rest

theorem ltLoop_localLength (a : Nat → E) :
    ∀ (missing : E) (l : List (Nat × Nat × Bool)) (n : Nat),
      Operations.localLength ((ltLoop a missing l) n).2 = ltLoopLen l := by
  intro missing l
  induction l generalizing missing with
  | nil => intro n; simp [ltLoop, pure_snd, Operations.localLength, ltLoopLen]
  | cons s rest ih =>
      intro n
      obtain ⟨hi, lo, bit⟩ := s
      cases bit with
      | false =>
          simp only [ltLoop, Bool.false_eq_true, if_false, bind_snd, witnessField_snd,
            assertZero_snd, localLength_witness, localLength_assert,
            Operations.append_localLength, Operations.localLength, ltLoopLen]
          have h := ih missing (n + 1 + 0)
          omega
      | true =>
          simp only [ltLoop, if_true, ltLoopLen]
          have h := ih (addMissing a hi lo missing) n
          omega

/-! ## Structural side conditions -/

theorem ltLoop_subcircuits (a : Nat → E) :
    ∀ (missing : E) (l : List (Nat × Nat × Bool)) (n : Nat),
      Operations.subcircuits ((ltLoop a missing l) n).2 = [] := by
  intro missing l
  induction l generalizing missing with
  | nil => intro n; simp [ltLoop, pure_snd, Operations.subcircuits]
  | cons s rest ih =>
      intro n
      obtain ⟨hi, lo, bit⟩ := s
      cases bit with
      | false =>
          simp only [ltLoop, Bool.false_eq_true, if_false, bind_snd, witnessField_snd,
            assertZero_snd, Operations.subcircuits_append, Operations.subcircuits,
            List.nil_append]
          exact ih _ _
      | true => simp only [ltLoop, if_true]; exact ih _ _

theorem ltLoop_interactions (a : Nat → E) :
    ∀ (missing : E) (l : List (Nat × Nat × Bool)) (n : Nat),
      Operations.interactions ((ltLoop a missing l) n).2 = [] := by
  intro missing l
  induction l generalizing missing with
  | nil => intro n; simp [ltLoop, pure_snd, Operations.interactions]
  | cons s rest ih =>
      intro n
      obtain ⟨hi, lo, bit⟩ := s
      cases bit with
      | false =>
          simp only [ltLoop, Bool.false_eq_true, if_false, bind_snd, witnessField_snd,
            assertZero_snd, Operations.interactions_append, Operations.interactions,
            List.nil_append]
          exact ih _ _
      | true => simp only [ltLoop, if_true]; exact ih _ _

theorem ltLoop_subcircuitsConsistent (a : Nat → E) :
    ∀ (missing : E) (l : List (Nat × Nat × Bool)) (n : Nat),
      Operations.SubcircuitsConsistent n ((ltLoop a missing l) n).2 := by
  intro missing l
  induction l generalizing missing with
  | nil =>
      intro n
      simp [ltLoop, pure_snd, Operations.SubcircuitsConsistent, Operations.forAll]
  | cons s rest ih =>
      intro n
      obtain ⟨hi, lo, bit⟩ := s
      cases bit with
      | false =>
          simp only [ltLoop, Bool.false_eq_true, if_false, bind_snd, witnessField_snd,
            assertZero_snd, localLength_witness, localLength_assert,
            Operations.SubcircuitsConsistent, Operations.forAll_append,
            Operations.localLength]
          refine ⟨?_, ?_, ?_⟩
          · simp [Operations.forAll]
          · simp [Operations.forAll]
          · simp only [Nat.zero_add, Nat.add_zero]
            rw [Nat.add_comm 1 n]
            exact ih _ _
      | true => simp only [ltLoop, if_true]; exact ih _ _

theorem ltLoop_channelsLawful (a : Nat → E) :
    ∀ (missing : E) (l : List (Nat × Nat × Bool)) (n : Nat),
      Operations.ChannelsLawful ((ltLoop a missing l) n).2 [] := by
  intro missing l
  induction l generalizing missing with
  | nil =>
      intro n
      simp [ltLoop, pure_snd, Operations.ChannelsLawful,
        Operations.subcircuitChannelsWithGuarantees, Operations.InChannelsOrGuarantees,
        Operations.SubcircuitChannelsLawful, Operations.forAllNoOffset, Operations.subcircuits]
  | cons s rest ih =>
      intro n
      obtain ⟨hi, lo, bit⟩ := s
      cases bit with
      | false =>
          simp only [ltLoop, Bool.false_eq_true, if_false, bind_snd, witnessField_snd,
            assertZero_snd]
          refine channelsLawful_append _ _ ?_ ?_
          · simp [Operations.ChannelsLawful, Operations.subcircuitChannelsWithGuarantees,
              Operations.InChannelsOrGuarantees, Operations.SubcircuitChannelsLawful,
              Operations.forAllNoOffset, Operations.subcircuits]
          · refine channelsLawful_append _ _ ?_ ?_
            · simp [Operations.ChannelsLawful, Operations.subcircuitChannelsWithGuarantees,
                Operations.InChannelsOrGuarantees, Operations.SubcircuitChannelsLawful,
                Operations.forAllNoOffset, Operations.subcircuits]
            · exact ih _ _
      | true => simp only [ltLoop, if_true]; exact ih _ _

theorem ltLoop_requirementsChannelsLawful (a : Nat → E) :
    ∀ (missing : E) (l : List (Nat × Nat × Bool)) (n : Nat),
      Operations.RequirementsChannelsLawful ((ltLoop a missing l) n).2 [] [] := by
  intro missing l
  induction l generalizing missing with
  | nil =>
      intro n
      simp only [ltLoop, pure_snd]
      exact requirementsChannelsLawful_of_nil (by simp [Operations.subcircuits])
        (by simp [Operations.interactions])
  | cons s rest ih =>
      intro n
      obtain ⟨hi, lo, bit⟩ := s
      cases bit with
      | false =>
          simp only [ltLoop, Bool.false_eq_true, if_false, bind_snd, witnessField_snd,
            assertZero_snd]
          exact requirementsChannelsLawful_of_nil
            (by simp [Operations.subcircuits_append, Operations.subcircuits,
              ltLoop_subcircuits])
            (by simp [Operations.interactions_append, Operations.interactions,
              ltLoop_interactions])
      | true => simp only [ltLoop, if_true]; exact ih _ _

/-! ## The bit accessor and the semantic spec -/

/-- Bit `k` of a 256-field input vector, with an arbitrary default outside the
range. -/
def ltBit (i : Var (fields 256) Fp) (k : Nat) : E :=
  if h : k < 256 then i[k] else cst 0

theorem eval_ltBit (env : Environment Fp) (i : Var (fields 256) Fp) (k : Nat) :
    Expression.eval env (ltBit i k) =
      if h : k < 256 then Expression.eval env i[k] else 0 := by
  unfold ltBit
  split
  · rfl
  · rfl

/-- The natural value of bit `k` of a concrete 256-field input. -/
def ltBitNat (i : fields 256 Fp) (k : Nat) : Fp := if h : k < 256 then i[k] else 0

/-- The comparator's semantic spec: the Boolean bits spell at most `bound`. -/
def ltOrderSpec (bound : Nat) (i : fields 256 Fp) : Prop :=
  prefVal (fun j => aNatOf (ltBitNat i) (255 - j)) 256 ≤ bound

/-- The comparator's assumption: every input field is Boolean. -/
def ltOrderAssumptions (i : fields 256 Fp) : Prop :=
  ∀ k : Fin 256, i[k] = 0 ∨ i[k] = 1

/-! ## `assertLtOrderOf` as a `FormalAssertion` -/

/-- `assertLtOrderOf` on a 256-field input vector. -/
def assertLtOrderOfMain (bound : Nat) (i : Var (fields 256) Fp) : Circuit Fp (Var unit Fp) :=
  assertLtOrderOf bound (ltBit i)

def assertLtOrderOfFamily (bound : Nat) :
    ExplicitCircuits (fun (i : Var (fields 256) Fp) => assertLtOrderOfMain bound i) where
  output := fun _ _ => ()
  localLength := fun _ _ => ltLoopLen (boundRunsOf bound)
  operations := fun i n => (assertLtOrderOf bound (ltBit i) n).2
  output_eq := by intro i n; rfl
  localLength_eq := by
    intro i n
    exact ltLoop_localLength _ _ _ n
  operations_eq := by intro i n; rfl
  subcircuitsConsistent := by
    intro i n
    exact ltLoop_subcircuitsConsistent _ _ _ n
  channelsWithGuarantees := fun _ _ => []
  channelsLawful := by
    intro i n
    exact ltLoop_channelsLawful _ _ _ n

instance (bound : Nat) : ExplicitCircuits.IsElaborated
    (fun (i : Var (fields 256) Fp) => assertLtOrderOfMain bound i)
    (assertLtOrderOfFamily bound) where
  localLength_eq := by intros; rfl
  channelsWithGuarantees_eq := by intros; rfl

instance (bound : Nat) : ElaboratedCircuit Fp (fields 256) unit (assertLtOrderOfMain bound) :=
  ElaboratedCircuit.fromExplicit (assertLtOrderOfFamily bound)
    (inferInstance : ExplicitCircuits.IsElaborated
      (fun (i : Var (fields 256) Fp) => assertLtOrderOfMain bound i)
      (assertLtOrderOfFamily bound))

theorem assertLtOrderOfMain_soundness (bound : Nat)
    (hpref : prefVal (boundNat bound) 256 = bound)
    (hcover : RunsCover bound 256 (boundRunsOf bound)) :
    FormalAssertion.Soundness Fp (assertLtOrderOfMain bound) ltOrderAssumptions
      (ltOrderSpec bound) := by
  circuit_proof_start
  simp only [assertLtOrderOfMain, assertLtOrderOf, bind_snd] at h_holds
  have hbits : ∀ k, Expression.eval env (ltBit input_var k) = 0 ∨
      Expression.eval env (ltBit input_var k) = 1 := by
    intro k
    rw [eval_ltBit]
    by_cases hk : k < 256
    · rw [dif_pos hk]
      have h1 : Expression.eval env input_var[k] = input[k] := by rw [← h_input]; simp
      rw [h1]
      exact h_assumptions ⟨k, hk⟩
    · rw [dif_neg hk]; simp
  have hres := assertLtOrderOf_sound bound (ltBit input_var) env i₀
    (fun k _ => hbits k) hpref hcover h_holds
  refine ⟨?_, ?_⟩
  · -- transport the conclusion to the concrete input
    refine le_trans (le_of_eq (prefVal_congr ?_)) hres
    intro j hj
    have hk : 255 - j < 256 := by omega
    have h1 : Expression.eval env input_var[255 - j] = input[255 - j] := by
      rw [← h_input]; simp
    simp only [aNatOf, ltBitNat, eval_ltBit, dif_pos hk, h1]
  · exact requirements_of_nil env _
      (by simp [assertLtOrderOfMain, assertLtOrderOf, bind_snd, Operations.interactions_append,
        ltLoop_interactions])
      (by simp [assertLtOrderOfMain, assertLtOrderOf, bind_snd, Operations.subcircuits_append,
        ltLoop_subcircuits])

theorem assertLtOrderOfMain_completeness (bound : Nat)
    (hpref : prefVal (boundNat bound) 256 = bound)
    (hcover : RunsCover bound 256 (boundRunsOf bound)) :
    FormalAssertion.Completeness Fp (assertLtOrderOfMain bound) ltOrderAssumptions
      (ltOrderSpec bound) := by
  circuit_proof_start
  simp only [assertLtOrderOfMain, assertLtOrderOf, bind_snd] at h_env ⊢
  have hbits : ∀ k, Expression.eval env.toEnvironment (ltBit input_var k) = 0 ∨
      Expression.eval env.toEnvironment (ltBit input_var k) = 1 := by
    intro k
    rw [eval_ltBit]
    by_cases hk : k < 256
    · rw [dif_pos hk]
      have h1 : Expression.eval env.toEnvironment input_var[k] = input[k] := by
        rw [← h_input]; simp
      rw [h1]
      exact h_assumptions ⟨k, hk⟩
    · rw [dif_neg hk]; simp
  have hle : prefVal
      (fun j => aNatOf (fun k => Expression.eval env.toEnvironment (ltBit input_var k))
        (255 - j)) 256 ≤ bound := by
    refine le_trans (le_of_eq (prefVal_congr ?_)) h_spec
    intro j hj
    have hk : 255 - j < 256 := by omega
    have h1 : Expression.eval env.toEnvironment input_var[255 - j] = input[255 - j] := by
      rw [← h_input]; simp
    simp only [aNatOf, ltBitNat, eval_ltBit, dif_pos hk, h1]
  have hm0 : Expression.eval env.toEnvironment (cst 0) =
      missAbove (fun k => Expression.eval env.toEnvironment (ltBit input_var k)) bound 256 := by
    simp only [circuit_norm, cst]
    unfold missAbove
    simp
  exact ltLoop_complete env _ (ltBit input_var) (fun k => rfl) hbits bound hpref hle
    (boundRunsOf bound) 256 (cst 0) i₀ (by omega) hcover hm0 h_env

/-- `assertLtOrderOf` bundled as a `FormalAssertion`. -/
def assertLtOrderOfAssertion (bound : Nat)
    (hpref : prefVal (boundNat bound) 256 = bound)
    (hcover : RunsCover bound 256 (boundRunsOf bound)) : FormalAssertion Fp (fields 256) where
  main := assertLtOrderOfMain bound
  Assumptions := ltOrderAssumptions
  Spec := ltOrderSpec bound
  soundness := assertLtOrderOfMain_soundness bound hpref hcover
  completeness := assertLtOrderOfMain_completeness bound hpref hcover
  requirementsChannelsLawful := by
    intro input offset
    simp only [assertLtOrderOfMain, assertLtOrderOf, bind_snd]
    exact ltLoop_requirementsChannelsLawful _ _ _ offset

/-! ## Structural side conditions for `ltLoopGuarded` -/

theorem ltLoopGuarded_localLength (a : Nat → E) (guard : E) :
    ∀ (missing : E) (l : List (Nat × Nat × Bool)) (n : Nat),
      Operations.localLength ((ltLoopGuarded a guard missing l) n).2 = ltLoopLen l := by
  intro missing l
  induction l generalizing missing with
  | nil => intro n; simp [ltLoopGuarded, pure_snd, Operations.localLength, ltLoopLen]
  | cons s rest ih =>
      intro n
      obtain ⟨hi, lo, bit⟩ := s
      cases bit with
      | false =>
          simp only [ltLoopGuarded, Bool.false_eq_true, if_false, bind_snd, witnessField_snd,
            assertZero_snd, localLength_witness, localLength_assert,
            Operations.append_localLength, Operations.localLength, ltLoopLen]
          have h := ih missing (n + 1 + 0)
          omega
      | true =>
          simp only [ltLoopGuarded, if_true, ltLoopLen]
          have h := ih (addMissing a hi lo missing) n
          omega

theorem ltLoopGuarded_subcircuits (a : Nat → E) (guard : E) :
    ∀ (missing : E) (l : List (Nat × Nat × Bool)) (n : Nat),
      Operations.subcircuits ((ltLoopGuarded a guard missing l) n).2 = [] := by
  intro missing l
  induction l generalizing missing with
  | nil => intro n; simp [ltLoopGuarded, pure_snd, Operations.subcircuits]
  | cons s rest ih =>
      intro n
      obtain ⟨hi, lo, bit⟩ := s
      cases bit with
      | false =>
          simp only [ltLoopGuarded, Bool.false_eq_true, if_false, bind_snd, witnessField_snd,
            assertZero_snd, Operations.subcircuits_append, Operations.subcircuits,
            List.nil_append]
          exact ih _ _
      | true => simp only [ltLoopGuarded, if_true]; exact ih _ _

theorem ltLoopGuarded_interactions (a : Nat → E) (guard : E) :
    ∀ (missing : E) (l : List (Nat × Nat × Bool)) (n : Nat),
      Operations.interactions ((ltLoopGuarded a guard missing l) n).2 = [] := by
  intro missing l
  induction l generalizing missing with
  | nil => intro n; simp [ltLoopGuarded, pure_snd, Operations.interactions]
  | cons s rest ih =>
      intro n
      obtain ⟨hi, lo, bit⟩ := s
      cases bit with
      | false =>
          simp only [ltLoopGuarded, Bool.false_eq_true, if_false, bind_snd, witnessField_snd,
            assertZero_snd, Operations.interactions_append, Operations.interactions,
            List.nil_append]
          exact ih _ _
      | true => simp only [ltLoopGuarded, if_true]; exact ih _ _

theorem ltLoopGuarded_subcircuitsConsistent (a : Nat → E) (guard : E) :
    ∀ (missing : E) (l : List (Nat × Nat × Bool)) (n : Nat),
      Operations.SubcircuitsConsistent n ((ltLoopGuarded a guard missing l) n).2 := by
  intro missing l
  induction l generalizing missing with
  | nil =>
      intro n
      simp [ltLoopGuarded, pure_snd, Operations.SubcircuitsConsistent, Operations.forAll]
  | cons s rest ih =>
      intro n
      obtain ⟨hi, lo, bit⟩ := s
      cases bit with
      | false =>
          simp only [ltLoopGuarded, Bool.false_eq_true, if_false, bind_snd, witnessField_snd,
            assertZero_snd, localLength_witness, localLength_assert,
            Operations.SubcircuitsConsistent, Operations.forAll_append,
            Operations.localLength]
          refine ⟨?_, ?_, ?_⟩
          · simp [Operations.forAll]
          · simp [Operations.forAll]
          · simp only [Nat.zero_add, Nat.add_zero]
            rw [Nat.add_comm 1 n]
            exact ih _ _
      | true => simp only [ltLoopGuarded, if_true]; exact ih _ _

theorem ltLoopGuarded_channelsLawful (a : Nat → E) (guard : E) :
    ∀ (missing : E) (l : List (Nat × Nat × Bool)) (n : Nat),
      Operations.ChannelsLawful ((ltLoopGuarded a guard missing l) n).2 [] := by
  intro missing l
  induction l generalizing missing with
  | nil =>
      intro n
      simp [ltLoopGuarded, pure_snd, Operations.ChannelsLawful,
        Operations.subcircuitChannelsWithGuarantees, Operations.InChannelsOrGuarantees,
        Operations.SubcircuitChannelsLawful, Operations.forAllNoOffset, Operations.subcircuits]
  | cons s rest ih =>
      intro n
      obtain ⟨hi, lo, bit⟩ := s
      cases bit with
      | false =>
          simp only [ltLoopGuarded, Bool.false_eq_true, if_false, bind_snd, witnessField_snd,
            assertZero_snd]
          refine channelsLawful_append _ _ ?_ ?_
          · simp [Operations.ChannelsLawful, Operations.subcircuitChannelsWithGuarantees,
              Operations.InChannelsOrGuarantees, Operations.SubcircuitChannelsLawful,
              Operations.forAllNoOffset, Operations.subcircuits]
          · refine channelsLawful_append _ _ ?_ ?_
            · simp [Operations.ChannelsLawful, Operations.subcircuitChannelsWithGuarantees,
                Operations.InChannelsOrGuarantees, Operations.SubcircuitChannelsLawful,
                Operations.forAllNoOffset, Operations.subcircuits]
            · exact ih _ _
      | true => simp only [ltLoopGuarded, if_true]; exact ih _ _

theorem ltLoopGuarded_requirementsChannelsLawful (a : Nat → E) (guard : E) :
    ∀ (missing : E) (l : List (Nat × Nat × Bool)) (n : Nat),
      Operations.RequirementsChannelsLawful ((ltLoopGuarded a guard missing l) n).2 [] [] := by
  intro missing l
  induction l generalizing missing with
  | nil =>
      intro n
      simp only [ltLoopGuarded, pure_snd]
      exact requirementsChannelsLawful_of_nil (by simp [Operations.subcircuits])
        (by simp [Operations.interactions])
  | cons s rest ih =>
      intro n
      obtain ⟨hi, lo, bit⟩ := s
      cases bit with
      | false =>
          simp only [ltLoopGuarded, Bool.false_eq_true, if_false, bind_snd, witnessField_snd,
            assertZero_snd]
          exact requirementsChannelsLawful_of_nil
            (by simp [Operations.subcircuits_append, Operations.subcircuits,
              ltLoopGuarded_subcircuits])
            (by simp [Operations.interactions_append, Operations.interactions,
              ltLoopGuarded_interactions])
      | true => simp only [ltLoopGuarded, if_true]; exact ih _ _

/-! ## `assertLtOrderGuardedOf` as a `FormalAssertion` -/

/-- Bit `k` of the 256-bit tail of a 257-field input (index `0` is the guard). -/
def ltBitG (i : Var (fields 257) Fp) (k : Nat) : E :=
  if h : k < 256 then i.get ⟨k + 1, by omega⟩ else cst 0

theorem eval_ltBitG (env : Environment Fp) (i : Var (fields 257) Fp) (k : Nat) :
    Expression.eval env (ltBitG i k) =
      if h : k < 256 then Expression.eval env (i.get ⟨k + 1, by omega⟩) else 0 := by
  unfold ltBitG
  split
  · rfl
  · rfl

/-- The natural value of bit `k` of a concrete 257-field input. -/
def ltBitGNat (i : fields 257 Fp) (k : Nat) : Fp :=
  if h : k < 256 then i.get ⟨k + 1, by omega⟩ else 0

/-- The guarded comparator's semantic spec. -/
def ltOrderGuardedSpec (bound : Nat) (i : fields 257 Fp) : Prop :=
  i[0] = 1 → prefVal (fun j => aNatOf (ltBitGNat i) (255 - j)) 256 ≤ bound

/-- The guarded comparator's assumption: guard and bits are Boolean. -/
def ltOrderGuardedAssumptions (i : fields 257 Fp) : Prop :=
  (i[0] = 0 ∨ i[0] = 1) ∧
    ∀ k : Fin 256, i.get ⟨k.val + 1, by omega⟩ = 0 ∨ i.get ⟨k.val + 1, by omega⟩ = 1

/-- `assertLtOrderGuardedOf` on a 257-field input vector. -/
def assertLtOrderGuardedOfMain (bound : Nat) (i : Var (fields 257) Fp) :
    Circuit Fp (Var unit Fp) :=
  assertLtOrderGuardedOf bound i[0] (ltBitG i)

def assertLtOrderGuardedOfFamily (bound : Nat) :
    ExplicitCircuits (fun (i : Var (fields 257) Fp) => assertLtOrderGuardedOfMain bound i) where
  output := fun _ _ => ()
  localLength := fun _ _ => ltLoopLen (boundRunsOf bound)
  operations := fun i n => (assertLtOrderGuardedOf bound i[0] (ltBitG i) n).2
  output_eq := by intro i n; rfl
  localLength_eq := by
    intro i n
    exact ltLoopGuarded_localLength _ _ _ _ n
  operations_eq := by intro i n; rfl
  subcircuitsConsistent := by
    intro i n
    exact ltLoopGuarded_subcircuitsConsistent _ _ _ _ n
  channelsWithGuarantees := fun _ _ => []
  channelsLawful := by
    intro i n
    exact ltLoopGuarded_channelsLawful _ _ _ _ n

instance (bound : Nat) : ExplicitCircuits.IsElaborated
    (fun (i : Var (fields 257) Fp) => assertLtOrderGuardedOfMain bound i)
    (assertLtOrderGuardedOfFamily bound) where
  localLength_eq := by intros; rfl
  channelsWithGuarantees_eq := by intros; rfl

instance (bound : Nat) : ElaboratedCircuit Fp (fields 257) unit
    (assertLtOrderGuardedOfMain bound) :=
  ElaboratedCircuit.fromExplicit (assertLtOrderGuardedOfFamily bound)
    (inferInstance : ExplicitCircuits.IsElaborated
      (fun (i : Var (fields 257) Fp) => assertLtOrderGuardedOfMain bound i)
      (assertLtOrderGuardedOfFamily bound))

theorem assertLtOrderGuardedOfMain_soundness (bound : Nat)
    (hpref : prefVal (boundNat bound) 256 = bound)
    (hcover : RunsCover bound 256 (boundRunsOf bound)) :
    FormalAssertion.Soundness Fp (assertLtOrderGuardedOfMain bound)
      ltOrderGuardedAssumptions (ltOrderGuardedSpec bound) := by
  circuit_proof_start
  simp only [assertLtOrderGuardedOfMain, assertLtOrderGuardedOf] at h_holds
  have hbits : ∀ k, Expression.eval env (ltBitG input_var k) = 0 ∨
      Expression.eval env (ltBitG input_var k) = 1 := by
    intro k
    rw [eval_ltBitG]
    by_cases hk : k < 256
    · rw [dif_pos hk]
      have h1 : Expression.eval env (input_var.get ⟨k + 1, by omega⟩) =
          input.get ⟨k + 1, by omega⟩ := by rw [← h_input]; simp
      rw [h1]
      exact h_assumptions.2 ⟨k, hk⟩
    · rw [dif_neg hk]; simp
  refine ⟨?_, ?_⟩
  · intro hguard
    have hg : Expression.eval env input_var[0] = 1 := by
      have h1 : Expression.eval env input_var[0] = input[0] := by rw [← h_input]; simp
      rw [h1]; exact hguard
    have hres := assertLtOrderGuardedOf_sound bound input_var[0] (ltBitG input_var) env i₀
      hg (fun k _ => hbits k) hpref hcover h_holds
    refine le_trans (le_of_eq (prefVal_congr ?_)) hres
    intro j hj
    have hk : 255 - j < 256 := by omega
    have h1 : Expression.eval env (input_var.get ⟨255 - j + 1, by omega⟩) =
        input.get ⟨255 - j + 1, by omega⟩ := by rw [← h_input]; simp
    simp only [aNatOf, ltBitGNat, eval_ltBitG, dif_pos hk, h1]
  · exact requirements_of_nil env _
      (by simp [assertLtOrderGuardedOfMain, assertLtOrderGuardedOf,
        Operations.interactions_append, ltLoopGuarded_interactions])
      (by simp [assertLtOrderGuardedOfMain, assertLtOrderGuardedOf,
        Operations.subcircuits_append, ltLoopGuarded_subcircuits])

theorem assertLtOrderGuardedOfMain_completeness (bound : Nat)
    (hpref : prefVal (boundNat bound) 256 = bound)
    (hcover : RunsCover bound 256 (boundRunsOf bound)) :
    FormalAssertion.Completeness Fp (assertLtOrderGuardedOfMain bound)
      ltOrderGuardedAssumptions (ltOrderGuardedSpec bound) := by
  circuit_proof_start
  simp only [assertLtOrderGuardedOfMain, assertLtOrderGuardedOf] at h_env ⊢
  have hg : Expression.eval env.toEnvironment input_var[0] = 0 ∨
      Expression.eval env.toEnvironment input_var[0] = 1 := by
    have h1 : Expression.eval env.toEnvironment input_var[0] = input[0] := by
      rw [← h_input]; simp
    rw [h1]; exact h_assumptions.1
  have hbits : ∀ k, Expression.eval env.toEnvironment (ltBitG input_var k) = 0 ∨
      Expression.eval env.toEnvironment (ltBitG input_var k) = 1 := by
    intro k
    rw [eval_ltBitG]
    by_cases hk : k < 256
    · rw [dif_pos hk]
      have h1 : Expression.eval env.toEnvironment (input_var.get ⟨k + 1, by omega⟩) =
          input.get ⟨k + 1, by omega⟩ := by rw [← h_input]; simp
      rw [h1]
      exact h_assumptions.2 ⟨k, hk⟩
    · rw [dif_neg hk]; simp
  have hle : Expression.eval env.toEnvironment input_var[0] = 1 →
      prefVal (fun j => aNatOf
        (fun k => Expression.eval env.toEnvironment (ltBitG input_var k)) (255 - j)) 256 ≤ bound := by
    intro hguard
    have h1 : Expression.eval env.toEnvironment input_var[0] = input[0] := by
      rw [← h_input]; simp
    refine le_trans (le_of_eq (prefVal_congr ?_)) (h_spec (by rw [← h1]; exact hguard))
    intro j hj
    have hk : 255 - j < 256 := by omega
    have h1 : Expression.eval env.toEnvironment (input_var.get ⟨255 - j + 1, by omega⟩) =
        input.get ⟨255 - j + 1, by omega⟩ := by rw [← h_input]; simp
    simp only [aNatOf, ltBitGNat, eval_ltBitG, dif_pos hk, h1]
  have hm0 : Expression.eval env.toEnvironment (cst 0) =
      missAbove (fun k => Expression.eval env.toEnvironment (ltBitG input_var k)) bound 256 := by
    simp only [circuit_norm, cst]
    unfold missAbove
    simp
  exact ltLoopGuarded_complete env _ (ltBitG input_var) (fun k => rfl) hbits bound
    input_var[0] hg hpref hle (boundRunsOf bound) 256 (cst 0) i₀ (by omega) hcover hm0 h_env

/-- `assertLtOrderGuardedOf` bundled as a `FormalAssertion`. -/
def assertLtOrderGuardedOfAssertion (bound : Nat)
    (hpref : prefVal (boundNat bound) 256 = bound)
    (hcover : RunsCover bound 256 (boundRunsOf bound)) : FormalAssertion Fp (fields 257) where
  main := assertLtOrderGuardedOfMain bound
  Assumptions := ltOrderGuardedAssumptions
  Spec := ltOrderGuardedSpec bound
  soundness := assertLtOrderGuardedOfMain_soundness bound hpref hcover
  completeness := assertLtOrderGuardedOfMain_completeness bound hpref hcover
  requirementsChannelsLawful := by
    intro input offset
    simp only [assertLtOrderGuardedOfMain, assertLtOrderGuardedOf]
    exact ltLoopGuarded_requirementsChannelsLawful _ _ _ _ offset

/-! ## The two concrete comparators used by the scalar phase -/

/-- The `r ≤ n - 1` comparator, bundled. -/
def assertLtOrderOfN : FormalAssertion Fp (fields 256) :=
  assertLtOrderOfAssertion nSubOne prefVal_boundNat_n runsCover_n

/-- The guarded `r ≤ (p - n) - 1` comparator, bundled. -/
def assertLtOrderGuardedOfP : FormalAssertion Fp (fields 257) :=
  assertLtOrderGuardedOfAssertion pSubNSubOne prefVal_boundNat_pn runsCover_pn

end StandardECDSA.Gadgets
