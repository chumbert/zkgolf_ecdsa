import ECDSA.EcdsaCircuit
import ECDSA.Pratt
import Challenge.Specs.ECDSAP256

namespace Challenge.Specs.ECDSAP256Projected

open Challenge.Specs.ECDSAP256

/-- Trusted projected ECDSA specification for 5 field inputs.

This is `RepresentationBridge.BoundLF` with `r.val, s.val`: the existential projection
of the unchanged Longfellow relation that binds the actual signature `(r, s)`.
-/
def Spec (pkX pkY digest r s : K) : Prop :=
  ∃ w : EcdsaWitness K,
    ValidEcdsaWitness w { X := pkX, Y := pkY } digest n params ∧
    natR (w.bi.map val3) = r.val ∧ n - natS (w.bi.map val3) = s.val

end Challenge.Specs.ECDSAP256Projected
