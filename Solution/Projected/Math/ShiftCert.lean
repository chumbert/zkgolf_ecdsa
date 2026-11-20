import Solution.Projected.Certs.Certs2
import Solution.Projected.Math.GroupSpec

/-! Shift point certificate: isolated proof that the shift point equals
(4 * ((4^128 - 1) / 3)) • G. -/
namespace Solution.Projected

open Challenge.Specs.ECDSAP256

-- The shift point theorem using the existing affine-chain facts
-- shiftX and shiftY are definitionally equal to cS895_x and cS895_y
theorem shift_pt : ∃ h, pt shiftX shiftY h = (4 * ((4^128 - 1) / 3)) • G :=
  ⟨cS895_curve, cS895_scalar⟩

end Solution.Projected
