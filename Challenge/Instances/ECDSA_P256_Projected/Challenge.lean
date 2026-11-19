/- Trusted comparator template, NOT a solution.
The sorry placeholders mirror the digest template. Submitted proofs
must not depend on sorryAx; no baseline circuit or par is claimed here. -/
import Challenge.Specs.ECDSAP256Projected
import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Challenge.Utils.CostR1CS
import Challenge.Utils.WitgenIR
import Challenge.Instances.ECDSA_P256_Projected.Interface
import Challenge.Instances.ECDSA_P256_Projected.Cost


/-!
Trusted challenge statements for the ECDSA P-256 projected-signature instance.

This file is the trusted boundary: it owns the input/output type and the
statements the implementation must prove. The implementation may be arbitrary,
but its exported proofs must have exactly these types.
-/

namespace Solution.ECDSA_P256_Projected

open Challenge.Instances.ECDSA_P256_Projected.Interface

noncomputable def honestHint : Input (F circuitPrime) → ProverHint (F circuitPrime) := sorry  -- TEMPLATE-SORRY

def ProverAssumptions := ProverAssumptionsWith honestHint

def main : Var Input (F circuitPrime) → Circuit (F circuitPrime) (Var Output (F circuitPrime)) := sorry  -- TEMPLATE-SORRY

instance elaborated : ElaboratedCircuit (F circuitPrime) Input Output main := sorry  -- TEMPLATE-SORRY

theorem soundness : GeneralFormalCircuit.Soundness (F circuitPrime) main Assumptions Spec := sorry  -- TEMPLATE-SORRY
theorem completeness : GeneralFormalCircuit.Completeness (F circuitPrime) main ProverAssumptions ProverSpec := sorry  -- TEMPLATE-SORRY

theorem mainCost : Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ := sorry  -- TEMPLATE-SORRY
theorem isR1CS : Challenge.CostR1CS.isR1CS main := sorry  -- TEMPLATE-SORRY
theorem witgenIsIR : Challenge.WitgenIR.witgenIsIR main := sorry  -- TEMPLATE-SORRY

theorem computableWitness : ∀ n input,
  ProverEnvironment.OnlyAccessedBelow n (fun env : ProverEnvironment (F circuitPrime) => eval env input) →
  Circuit.ComputableWitnesses (main input) n := sorry  -- TEMPLATE-SORRY

theorem requirementsChannelsLawful : ∀ input offset,
  ((main input).operations offset).RequirementsChannelsLawful
    elaborated.channelsWithGuarantees [] := sorry  -- TEMPLATE-SORRY

def formalCircuit : GeneralFormalCircuit (F circuitPrime) Input Output :=
  {
    main := main
    requirementsChannelsLawful := requirementsChannelsLawful
    Assumptions := Assumptions
    Spec := Spec
    ProverAssumptions := ProverAssumptions
    ProverSpec := ProverSpec
    soundness := soundness
    completeness := completeness
  }

end Solution.ECDSA_P256_Projected
