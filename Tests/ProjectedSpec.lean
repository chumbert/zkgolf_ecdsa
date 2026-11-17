import Challenge.Specs.ECDSAP256Projected
import Baseline.Projected.RepresentationIndependent

/- The trusted projected spec is definitionally the Longfellow bound relation
on the projected signature values. -/
example (pkX pkY digest r s : Challenge.Specs.ECDSAP256.K) :
    Challenge.Specs.ECDSAP256Projected.Spec pkX pkY digest r s =
      RepresentationBridge.BoundLF ⟨pkX, pkY⟩ digest r.val s.val
        Challenge.Specs.ECDSAP256.n Challenge.Specs.ECDSAP256.params := rfl
