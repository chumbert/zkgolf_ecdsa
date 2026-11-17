import ECDSA.EcdsaCircuit
import ECDSA.Pratt
import Challenge.Specs.ECDSAP256

namespace Challenge.Specs.ECDSAP256Projected

open Challenge.Specs.ECDSAP256

/-- Projected-signature Longfellow circuit relation: the public inputs are the
public key, the digest, and the signature values `r` and `s` directly (as field
elements), with `s` given as `n - t` for the reconstructed `t`. -/
def Spec (pkX pkY digest r s : K) : Prop :=
  ∃ w : EcdsaWitness K,
    ValidEcdsaWitness w ({ X := pkX, Y := pkY } : AffinePoint K) digest n params ∧
    natR (w.bi.map val3) = r.val ∧
    n - natS (w.bi.map val3) = s.val

end Challenge.Specs.ECDSAP256Projected
