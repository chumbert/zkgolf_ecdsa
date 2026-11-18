/-
# Explicit metadata for a stuck `if` between two circuits

`mat`'s allocation branch is `if deg a = 0 ∨ deg b = 0 then … else …`.  When both
factors are opaque expressions the condition does not reduce, so
`elaborate_circuit` cannot split it.  This instance lets the tactic treat the two
branches as sub-circuits and combine their metadata.

The channel metadata of the two branches is *unioned* rather than selected by the
condition.  A union is still a lawful superset, and it keeps
`channelsWithGuarantees` syntactically offset-independent, which is what Clean's
`ExplicitCircuits.IsElaborated` side condition needs.

Task T05 / T10 (framework half).
-/

import StandardECDSA.Gadgets.Field
import Clean.Circuit.Explicit

namespace StandardECDSA.Gadgets

/-- `ChannelsLawful` is monotone in the channel list. -/
theorem channelsLawful_mono {ops : Operations Fp} {c c' : List (RawChannel Fp)}
    (h : ops.ChannelsLawful c) (hsub : c ⊆ c') : ops.ChannelsLawful c' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨List.Subset.trans h1 hsub, fun env => (h2 env).mono hsub, h3⟩

@[instance_reducible, explicit_circuit_constructor]
def ExplicitCircuit.from_ite {α : Type} {c : Prop} [Decidable c]
    {A B : Circuit Fp α}
    (hA : ExplicitCircuit (F := Fp) A) (hB : ExplicitCircuit (F := Fp) B) :
    ExplicitCircuit (F := Fp) (if c then A else B) where
  output n := if c then hA.output n else hB.output n
  localLength n := if c then hA.localLength n else hB.localLength n
  operations n := if c then hA.operations n else hB.operations n
  output_eq n := by by_cases h : c <;> simp [h, hA.output_eq, hB.output_eq]
  localLength_eq n := by by_cases h : c <;> simp [h, hA.localLength_eq, hB.localLength_eq]
  operations_eq n := by by_cases h : c <;> simp [h, hA.operations_eq, hB.operations_eq]
  subcircuitsConsistent n := by
    by_cases h : c <;> simp [h, hA.subcircuitsConsistent, hB.subcircuitsConsistent]
  channelsWithGuarantees n := hA.channelsWithGuarantees n ++ hB.channelsWithGuarantees n
  channelsLawful n := by
    by_cases h : c
    · rw [if_pos h]
      exact channelsLawful_mono (hA.channelsLawful n) (List.subset_append_left _ _)
    · rw [if_neg h]
      exact channelsLawful_mono (hB.channelsLawful n) (List.subset_append_right _ _)

instance {α : Type} {c : Prop} [Decidable c] {A B : Circuit Fp α}
    [hA : ExplicitCircuit (F := Fp) A] [hB : ExplicitCircuit (F := Fp) B] :
    ExplicitCircuit (F := Fp) (if c then A else B) :=
  ExplicitCircuit.from_ite hA hB

end StandardECDSA.Gadgets
