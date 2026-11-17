import Challenge.Specs.ECDSAP256Projected
import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving

namespace Challenge.Instances.ECDSA_P256_Projected.Interface

/-- Projected-signature inputs: public key, digest, and signature values `r`, `s`
as field elements. No witness wires are public. -/
structure Input (F : Type) where
  pkX : F
  pkY : F
  digest : F
  r : F
  s : F
  deriving ProvableStruct

abbrev Output : TypeMap := unit
abbrev circuitPrime : ℕ := Challenge.Specs.ECDSAP256.p

namespace Solution.ECDSA_P256_Projected

/-- Placeholder for the submission-supplied honest hint generator. -/
def honestHint (input : Challenge.Instances.ECDSA_P256_Projected.Interface.Input
    (F Challenge.Instances.ECDSA_P256_Projected.Interface.circuitPrime)) :
    ProverHint (F Challenge.Instances.ECDSA_P256_Projected.Interface.circuitPrime) := sorry

end Solution.ECDSA_P256_Projected

namespace Challenge.Instances.ECDSA_P256_Projected.Interface

/-- No caller assumptions: the circuit itself constrains key and signature validity. -/
def Assumptions (_input : Input (F circuitPrime)) (_data : ProverData (F circuitPrime)) : Prop := True

def Spec (input : Input (F circuitPrime)) (_output : Output (F circuitPrime))
    (_data : ProverData (F circuitPrime)) : Prop :=
  Challenge.Specs.ECDSAP256Projected.Spec input.pkX input.pkY input.digest input.r input.s

def ProverAssumptions (input : Input (F circuitPrime)) (data : ProverData (F circuitPrime))
    (hint : ProverHint (F circuitPrime)) : Prop :=
  Spec input () data ∧ hint = Solution.ECDSA_P256_Projected.honestHint input

def ProverSpec (_input : Input (F circuitPrime)) (_output : Output (F circuitPrime))
    (_hint : ProverHint (F circuitPrime)) : Prop := True

end Challenge.Instances.ECDSA_P256_Projected.Interface
