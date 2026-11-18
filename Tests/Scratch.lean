import Baseline.Projected.P256Bridge

open Challenge.Specs.ECDSAP256

example (r ry : K) (h : ry^2 = r^3 + params.a*r + params.b) :
    ry^2 = (r.val : K)^3 + params.a*(r.val : K) + params.b := by
  rw [ZMod.natCast_zmod_val r]; exact h

example (r ry : K) (h : ry^2 = (r.val : K)^3 + params.a*(r.val : K) + params.b) :
    ry^2 = r^3 + params.a*r + params.b := by
  rw [ZMod.natCast_zmod_val r] at h; exact h
