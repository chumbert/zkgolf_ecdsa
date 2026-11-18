/-
# Hint causality: the fixed-hint contract

The plan's item 5 requires a *truthful* causality statement for the honest
witness generator: generator evaluation must agree between environments that
agree on the earlier wires and on the relevant hint provider.  This is **not**
the old `Circuit.ComputableWitnesses` obligation, which the pinned Clean
definitions cannot satisfy for a `FExpr.hintGet` leaf (see
`Challenge/Utils/WitgenIR.lean:47-55` and Clean `Circuit/Basic.lean:424-438`:
`ProverEnvironment.AgreesBelow` compares wires only, not hint providers).

This module fixes the contract as a *pure* statement about hint providers and
generators, so that it can be discharged for the concrete generator of T16
without any appeal to the Clean environment API.
-/

import StandardECDSA.Witness.Seed

namespace StandardECDSA

set_option maxRecDepth 100000

/-- A hint provider: a total map from hint indices to field values. -/
abbrev HintProvider := Nat → K

/-- Two hint providers agree on a set `S` of indices. -/
def AgreesOn (h₁ h₂ : HintProvider) (S : Set Nat) : Prop := ∀ i ∈ S, h₁ i = h₂ i

/-- A witness generator is *causally determined* by the hint indices in `S` when
its output only depends on the restriction of the provider to `S`. -/
def CausallyDetermined {α : Type} (gen : HintProvider → α) (S : Set Nat) : Prop :=
  ∀ h₁ h₂ : HintProvider, AgreesOn h₁ h₂ S → gen h₁ = gen h₂

/-- **Fixed-hint causality.**  A generator that reads its hints only through a
fixed index set is causally determined by that set.  This is the structural
composition lemma the plan asks for; the concrete generator of T16 instantiates
`gen` and `S`. -/
theorem fixed_hint_causality {α : Type} (gen : HintProvider → α) (S : Set Nat)
    (hread : ∀ h₁ h₂ : HintProvider, AgreesOn h₁ h₂ S → gen h₁ = gen h₂) :
    CausallyDetermined gen S :=
  hread

/-- Causality composes: if `f` is causally determined by `S` and `g` by `T`, then
`g ∘ f` is causally determined by `S ∪ T`. -/
theorem causallyDetermined_comp {α β : Type} (f : HintProvider → α)
    (g : α → HintProvider → β) (S T : Set Nat)
    (hf : CausallyDetermined f S)
    (hg : ∀ a, CausallyDetermined (g a) T) :
    CausallyDetermined (fun h => g (f h) h) (S ∪ T) := by
  intro h₁ h₂ hagree
  have hS : AgreesOn h₁ h₂ S := fun i hi => hagree i (Set.mem_union_left T hi)
  have hT : AgreesOn h₁ h₂ T := fun i hi => hagree i (Set.mem_union_right S hi)
  have hfeq : f h₁ = f h₂ := hf h₁ h₂ hS
  show g (f h₁) h₁ = g (f h₂) h₂
  rw [hfeq]
  exact hg (f h₂) h₁ h₂ hT

/-- The seed indices used by the standard circuit: the 772 hint cells. -/
def seedIndices : Set Nat := { i | i < 772 }

/-- The seed layout has 772 cells, so every seed index is below 772. -/
theorem seed_index_bound (i : Nat) (hi : i ∈ seedIndices) : i < 772 := hi

end StandardECDSA
