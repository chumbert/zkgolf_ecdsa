import Challenge.Specs.ECDSAP256Projected
import Baseline.Projected.BoundLF

namespace Tests.ProjectedSpec

open Challenge.Specs.ECDSAP256Projected
open Challenge.Specs.ECDSAP256

/-- The projected Spec unfolds to RepresentationBridge.BoundLF. -/
theorem spec_iff_boundLF (pkX pkY digest r s : K) :
    Challenge.Specs.ECDSAP256Projected.Spec pkX pkY digest r s ↔
    RepresentationBridge.BoundLF { X := pkX, Y := pkY } digest r.val s.val n params := by
  rfl

end Tests.ProjectedSpec
