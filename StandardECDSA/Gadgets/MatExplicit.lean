/-
# Explicit metadata for the `mat` lowering gadget

`mat` is a *recursive* circuit: it walks the expression tree and allocates one
wire per non-constant product.  Clean's `elaborate_circuit` tactic cannot infer
an `ExplicitCircuit` instance for it, because the recursion is stuck as soon as
`mat` is applied to a variable expression (the tactic can only unfold a wrapper
whose argument is already a constructor application).

This file supplies the missing instance by hand: three structurally recursive
functions `matLen` / `matOut` / `matOps` mirroring `mat`, together with the
three agreement lemmas and the two structural side conditions.  With the
instance in scope, every gadget that calls `mat` (`sel`, `muxConst4`, `mux4`,
`affDouble`, `elm`, `elmTo`, `isOnCurve`, `pointEquality`, `assertZeroLazy` and
all three phases) becomes elaboratable.

Task T05 / T10 (framework half).
-/

import StandardECDSA.Gadgets.Field
import Clean.Circuit.Explicit

namespace StandardECDSA.Gadgets

/-! ## Projection-level lemmas

`Circuit` is a function `ℕ → α × Operations F`, so `Circuit.output` /
`Circuit.localLength` / `Circuit.operations` are reducible projections.  Working
directly with `.1` / `.2` keeps the rewriting predictable: the `Circuit`-level
accessors are definitionally equal to the projections, so a lemma stated at the
projection level is accepted wherever the accessor form is expected. -/

theorem bind_fst {α β : Type} (f : Circuit Fp α) (g : α → Circuit Fp β) (n : ℕ) :
    ((f >>= g) n).1 = (g ((f n).1) (n + Operations.localLength ((f n).2))).1 := rfl

theorem bind_snd {α β : Type} (f : Circuit Fp α) (g : α → Circuit Fp β) (n : ℕ) :
    ((f >>= g) n).2 =
      (f n).2 ++ (g ((f n).1) (n + Operations.localLength ((f n).2))).2 := rfl

theorem witnessField_fst (e : Witgen.FExpr Fp) (n : ℕ) :
    ((witnessField e) n).1 = .var ⟨n⟩ := rfl

theorem witnessField_snd (e : Witgen.FExpr Fp) (n : ℕ) :
    ((witnessField e) n).2 = [.witness 1 (.ofFExpr e)] := rfl

theorem assertZero_fst (e : E) (n : ℕ) : ((assertZero e) n).1 = () := rfl

theorem assertZero_snd (e : E) (n : ℕ) : ((assertZero e) n).2 = [.assert e] := rfl

theorem pure_fst {α : Type} (a : α) (n : ℕ) : ((pure a : Circuit Fp α) n).1 = a := rfl

theorem pure_snd {α : Type} (a : α) (n : ℕ) : ((pure a : Circuit Fp α) n).2 = [] := rfl

theorem map_fst {α β : Type} (f : α → β) (c : Circuit Fp α) (n : ℕ) :
    ((f <$> c) n).1 = f ((c n).1) := rfl

theorem map_snd {α β : Type} (f : α → β) (c : Circuit Fp α) (n : ℕ) :
    ((f <$> c) n).2 = (c n).2 := rfl

/-! ## The three mirror functions -/

/-- Local length of `mat e`.  It does not depend on the offset: the branch
condition `deg a = 0 ∨ deg b = 0` is a property of the expression alone.  This
offset-independence is what makes `mat` an `ExplicitCircuit` in the sense of
Clean's `ExplicitCircuits.IsElaborated` side condition. -/
def matLen : E → ℕ
  | .var _ => 0
  | .const _ => 0
  | .add a b => matLen a + matLen b
  | .mul a b =>
      if deg a = 0 ∨ deg b = 0 then matLen a + matLen b else matLen a + matLen b + 1

/-- Output expression of `mat e` started at offset `n`. -/
def matOut : E → ℕ → E
  | .var v, _ => .var v
  | .const c, _ => .const c
  | .add a b, n => matOut a n + matOut b (n + matLen a)
  | .mul a b, n =>
      if deg a = 0 ∨ deg b = 0 then matOut a n * matOut b (n + matLen a)
      else .var ⟨n + matLen a + matLen b⟩

/-- Operations of `mat e` started at offset `n`. -/
def matOps : E → ℕ → Operations Fp
  | .var _, _ => []
  | .const _, _ => []
  | .add a b, n => matOps a n ++ matOps b (n + matLen a)
  | .mul a b, n =>
      matOps a n ++ (matOps b (n + matLen a) ++
        (if deg a = 0 ∨ deg b = 0 then []
         else [.witness 1 (.ofFExpr (.mul (.expr (matOut a n))
                                            (.expr (matOut b (n + matLen a))))),
               .assert (matOut a n * matOut b (n + matLen a) -
                 .var ⟨n + matLen a + matLen b⟩)]))

/-- Local length of the explicit operation list. -/
theorem matOps_localLength (e : E) : ∀ n, (matOps e n).localLength = matLen e := by
  induction e with
  | var v => intro n; rfl
  | const c => intro n; rfl
  | add a b iha ihb =>
      intro n
      simp only [matOps, matLen, Operations.append_localLength, iha, ihb]
  | mul a b iha ihb =>
      intro n
      simp only [matOps, matLen, Operations.append_localLength, iha, ihb,
        Operations.localLength, List.nil_append, List.append_nil]
      split <;> simp [Operations.localLength, Nat.add_assoc]

/-! ## Agreement lemmas -/

theorem mat_localLength_eq (e : E) : ∀ n, Operations.localLength ((mat e) n).2 = matLen e := by
  induction e with
  | var v => intro n; rfl
  | const c => intro n; rfl
  | add a b iha ihb =>
      intro n
      simp only [mat, matLen, bind_snd, pure_snd, Operations.localLength,
        Operations.append_localLength, List.nil_append, List.append_nil, iha, ihb]
  | mul a b iha ihb =>
      intro n
      simp only [mat, matLen, bind_snd, pure_snd, witnessField_snd, assertZero_snd,
        Operations.localLength, Operations.append_localLength, List.nil_append,
        List.append_nil, iha, ihb]
      split <;> simp [pure_snd, witnessField_snd, assertZero_snd, bind_snd, map_snd,
        Operations.localLength, Operations.append_localLength, List.nil_append, List.append_nil,
        Nat.add_assoc]

theorem mat_output_eq (e : E) : ∀ n, ((mat e) n).1 = matOut e n := by
  induction e with
  | var v => intro n; rfl
  | const c => intro n; rfl
  | add a b iha ihb =>
      intro n
      simp only [mat, matOut, bind_fst, pure_fst, mat_localLength_eq, matOps_localLength, iha, ihb]
  | mul a b iha ihb =>
      intro n
      simp only [mat, matOut, bind_fst, pure_fst, witnessField_fst, assertZero_fst,
        mat_localLength_eq, matOps_localLength, iha, ihb]
      split <;> rfl

theorem mat_operations_eq (e : E) : ∀ n, ((mat e) n).2 = matOps e n := by
  induction e with
  | var v => intro n; rfl
  | const c => intro n; rfl
  | add a b iha ihb =>
      intro n
      simp only [mat, matOps, bind_snd, pure_snd, mat_localLength_eq, matOps_localLength,
        mat_output_eq, iha, ihb, List.nil_append, List.append_nil]
  | mul a b iha ihb =>
      intro n
      simp only [mat, matOps, bind_snd, pure_snd, witnessField_snd, assertZero_snd,
        mat_localLength_eq, matOps_localLength, mat_output_eq, iha, ihb,
        List.nil_append, List.append_nil]
      split <;> rfl

/-! ## Structural side conditions -/

theorem matOps_subcircuitsConsistent (e : E) : ∀ n, (matOps e n).SubcircuitsConsistent n := by
  induction e with
  | var v => intro n; trivial
  | const c => intro n; trivial
  | add a b iha ihb =>
      intro n
      simp only [matOps, Operations.SubcircuitsConsistent, Operations.forAll_append,
        Operations.localLength, matOps_localLength]
      refine ⟨iha n, ?_⟩
      rw [Nat.add_comm (matLen a) n]
      exact ihb (n + matLen a)
  | mul a b iha ihb =>
      intro n
      simp only [matOps, Operations.SubcircuitsConsistent, Operations.forAll_append,
        Operations.localLength, matOps_localLength]
      refine ⟨iha n, ?_, ?_⟩
      · rw [Nat.add_comm (matLen a) n]
        exact ihb (n + matLen a)
      split
      · trivial
      · simp [Operations.SubcircuitsConsistent, Operations.forAll, Operations.localLength]

theorem matOps_channelsLawful (e : E) : ∀ n, (matOps e n).ChannelsLawful [] := by
  induction e with
  | var v =>
      intro n
      simp [matOps, Operations.ChannelsLawful, Operations.subcircuitChannelsWithGuarantees,
        Operations.InChannelsOrGuarantees, Operations.SubcircuitChannelsLawful,
        Operations.forAllNoOffset, Operations.subcircuits]
  | const c =>
      intro n
      simp [matOps, Operations.ChannelsLawful, Operations.subcircuitChannelsWithGuarantees,
        Operations.InChannelsOrGuarantees, Operations.SubcircuitChannelsLawful,
        Operations.forAllNoOffset, Operations.subcircuits]
  | add a b iha ihb =>
      intro n
      simp only [matOps]
      exact Operations.channelsLawful_append_of_channelsLawful (iha n) (ihb (n + matLen a))
  | mul a b iha ihb =>
      intro n
      simp only [matOps]
      refine Operations.channelsLawful_append_of_channelsLawful (iha n) ?_
      refine Operations.channelsLawful_append_of_channelsLawful (ihb (n + matLen a)) ?_
      split
      · simp [Operations.ChannelsLawful, Operations.subcircuitChannelsWithGuarantees,
          Operations.InChannelsOrGuarantees, Operations.SubcircuitChannelsLawful,
          Operations.forAllNoOffset, Operations.subcircuits]
      · simp [Operations.ChannelsLawful, Operations.subcircuitChannelsWithGuarantees,
          Operations.InChannelsOrGuarantees, Operations.SubcircuitChannelsLawful,
          Operations.forAllNoOffset, Operations.subcircuits]

theorem mat_subcircuitsConsistent (e : E) :
    ∀ n, (Circuit.operations (mat e) n).SubcircuitsConsistent n := by
  intro n
  show Operations.SubcircuitsConsistent n ((mat e) n).2
  rw [mat_operations_eq e n]
  exact matOps_subcircuitsConsistent e n

theorem mat_channelsLawful (e : E) :
    ∀ n, (Circuit.operations (mat e) n).ChannelsLawful [] := by
  intro n
  show Operations.ChannelsLawful ((mat e) n).2 []
  rw [mat_operations_eq e n]
  exact matOps_channelsLawful e n

/-! ## The instance -/

@[instance_reducible, explicit_circuit_constructor]
def matExplicit (e : E) : ExplicitCircuit (mat e) where
  output := matOut e
  localLength := fun _ => matLen e
  operations := matOps e
  output_eq := mat_output_eq e
  localLength_eq := mat_localLength_eq e
  operations_eq := mat_operations_eq e
  subcircuitsConsistent := mat_subcircuitsConsistent e
  channelsWithGuarantees := fun _ => []
  channelsLawful := mat_channelsLawful e

instance (e : E) : ExplicitCircuit (mat e) := matExplicit e

end StandardECDSA.Gadgets
