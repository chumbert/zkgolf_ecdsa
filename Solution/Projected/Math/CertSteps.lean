import Solution.Projected.Math.GroupSpec

/-! Step-level certificates for P-256 constant chains: bridges from `decide`
checks on `.val` (Nat) equations to mathlib group equations via `AffineBridge`. -/
namespace Solution.Projected

open Challenge.Specs.ECDSAP256

/-- A curve equation from a Nat-level certificate. -/
lemma curve_of_nat {x y : K}
    (h : (y^2).val = (x^3 + params.a*x + params.b).val) :
    y^2 = x^3 + params.a*x + params.b :=
  ZMod.val_injective p h

/-- One affine addition step, certified by Nat-level (`val`) equations. -/
lemma add_step {l xA yA xB yB xR yR : K}
    (hA : yA^2 = xA^3 + params.a*xA + params.b)
    (hB : yB^2 = xB^3 + params.a*xB + params.b)
    (hR : yR^2 = xR^3 + params.a*xR + params.b)
    (c1 : (l * (xB - xA)).val = (yB - yA).val)
    (c2 : (l * l).val = (xA + xB + xR).val)
    (c3 : (l * (xA - xR)).val = (yA + yR).val)
    (cd : xB ≠ xA) :
    pt xR yR hR = pt xA yA hA + pt xB yB hB := by
  refine Baseline.Projected.AffineBridge.affine_add_eq_group params xA yA xB yB xR yR l
    (Baseline.Projected.AffineBridge.short_nonsingular params xA yA hA)
    (Baseline.Projected.AffineBridge.short_nonsingular params xB yB hB)
    (Baseline.Projected.AffineBridge.short_nonsingular params xR yR hR) ?_ ?_ ?_ ?_
  · intro h; exact cd (sub_eq_zero.mp h)
  · exact ZMod.val_injective p c1
  · exact ZMod.val_injective p c2
  · exact ZMod.val_injective p c3

/-- One affine doubling step, certified by Nat-level (`val`) equations. -/
lemma double_step {l x y xR yR : K}
    (hA : y^2 = x^3 + params.a*x + params.b)
    (hR : yR^2 = xR^3 + params.a*xR + params.b)
    (c0 : (2 * y).val ≠ 0)
    (c1 : ((2 * y) * l).val = (3 * x^2 + params.a).val)
    (c2 : (l * l).val = (2 * x + xR).val)
    (c3 : (l * (x - xR)).val = (y + yR).val) :
    pt xR yR hR = 2 • pt x y hA := by
  refine Baseline.Projected.AffineBridge.affine_double_eq_group params x y xR yR l
    (Baseline.Projected.AffineBridge.short_nonsingular params x y hA)
    (Baseline.Projected.AffineBridge.short_nonsingular params xR yR hR) ?_ ?_ ?_ ?_
  · intro h; exact c0 (by rw [h]; rfl)
  · exact ZMod.val_injective p c1
  · exact ZMod.val_injective p c2
  · exact ZMod.val_injective p c3

lemma pt_ne_zero {x y : K} (h : y^2 = x^3 + params.a*x + params.b) : pt x y h ≠ 0 := by
  intro h0
  nomatch h0

end Solution.Projected
