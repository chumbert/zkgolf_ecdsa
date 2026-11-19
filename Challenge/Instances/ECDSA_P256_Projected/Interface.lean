import Challenge.Specs.ECDSAP256Projected
import Clean.Circuit
import Clean.Utils.Tactics.ProvableStructDeriving

namespace Challenge.Instances.ECDSA_P256_Projected.Interface

open Challenge.Specs.ECDSAP256

/-- Projected ECDSA inputs: only the public signature components.
The circuit must existentially prove a valid Longfellow witness matching (r, s). -/
structure Input (F : Type) where
  pkX : F
  pkY : F
  digest : F
  r : F
  s : F
  deriving ProvableStruct

abbrev Output : TypeMap := unit
abbrev circuitPrime : ℕ := p

/-- No caller assumptions beyond the field being correct. -/
def Assumptions (_input : Input (F circuitPrime)) (_data : ProverData (F circuitPrime)) : Prop := True

/-- Projected spec: existential Longfellow witness with matching (r, s). -/
def Spec (input : Input (F circuitPrime)) (_output : Output (F circuitPrime))
    (_data : ProverData (F circuitPrime)) : Prop :=
  Challenge.Specs.ECDSAP256Projected.Spec input.pkX input.pkY input.digest input.r input.s

def ProverAssumptionsWith (honestHint : Input (F circuitPrime) → ProverHint (F circuitPrime))
    (input : Input (F circuitPrime)) (data : ProverData (F circuitPrime))
    (hint : ProverHint (F circuitPrime)) : Prop :=
  Spec input () data ∧ hint = honestHint input

def ProverSpec (_input : Input (F circuitPrime)) (_output : Output (F circuitPrime))
    (_hint : ProverHint (F circuitPrime)) : Prop := True

end Challenge.Instances.ECDSA_P256_Projected.Interface
