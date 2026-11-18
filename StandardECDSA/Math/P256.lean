/-
# P-256 field and curve facts

This module provides the concrete P-256 base field, curve parameters, and the
basic algebraic facts needed by the standard ECDSA proof.

Every fact here is *kernel checked*: the proofs use `decide` (kernel reduction)
or are transported from the vendored Longfellow certificates.  No `native_decide`
is used anywhere in this development, because `native_decide` introduces a fresh
axiom (`..._native.native_decide.ax_...`) and the release audit only permits
`propext`, `Classical.choice` and `Quot.sound`.
-/

import StandardECDSA.Spec
import ECDSA.EC
import ECDSA.P256NoRoot
import ECDSA.P256OrderPratt

namespace StandardECDSA.Math

open StandardECDSA

set_option maxRecDepth 100000
set_option exponentiation.threshold 400

/-! ## Base field primality -/

instance : Fact (Nat.Prime p) :=
  ⟨ECDSA.prime_115792089210356248762697446949407573530086143415290314195533631308867097853951⟩

/-! ## The generator -/

/-- The P-256 generator as an affine point. -/
def gAffine : AffinePoint K := { X := params.gx, Y := params.gy }

/-- The P-256 generator as a projective point `(gx, gy, 1)`. -/
def gPoint : ProjectivePoint K := { X := params.gx, Y := params.gy, Z := 1 }

/-- The P-256 generator is on the curve. -/
theorem generator_on_curve : gAffine.IsOnCurve params := by
  unfold AffinePoint.IsOnCurve gAffine params
  decide

/-- The P-256 generator, in projective coordinates, is a valid curve point. -/
theorem gPoint_on_curve : gPoint.IsOnCurve params := by
  refine ⟨?_, ?_⟩
  · unfold ProjectivePoint.SatisfiesCurveEquation gPoint
    dsimp
    simpa [AffinePoint.IsOnCurve, gAffine] using generator_on_curve
  · intro h
    have hz := congr_arg ProjectivePoint.Z h
    simp [gPoint] at hz

/-! ## Nonsingularity -/

/-- The P-256 curve is nonsingular: its discriminant `4a³ + 27b²` is nonzero. -/
theorem discriminant_ne_zero : 4 * (params.a : K) ^ 3 + 27 * (params.b : K) ^ 2 ≠ 0 := by
  unfold params
  decide

/-! ## No rational two-torsion -/

/-- The Longfellow certificate `aa`/`bb` agrees with our `params.a`/`params.b`. -/
theorem aa_eq : ((ECDSA.aa : Nat) : K) = params.a := by decide

theorem bb_eq : ((ECDSA.bb : Nat) : K) = params.b := by decide

/-- The P-256 cubic `x³ + a·x + b` has no root in `F_p`, i.e. the curve has no
nonzero point of order two.  Transported from the vendored kernel-checked
certificate `ECDSA.p256_cubic_no_root`. -/
theorem no_two_torsion (x : K) : x ^ 3 + params.a * x + params.b ≠ 0 := by
  intro h
  apply ECDSA.p256_cubic_no_root x
  rw [← aa_eq, ← bb_eq] at h
  exact h

/-! ## Concrete arithmetic inequalities -/

/-- The group order is below the field prime. -/
theorem n_lt_p : n < p := by decide

/-- The field prime is below twice the group order. -/
theorem p_lt_two_n : p < 2 * n := by decide

/-- `2p + 1 < 3n`: the key inequality of the Hasse-free order argument. -/
theorem two_p_plus_one_lt_three_n : 2 * p + 1 < 3 * n := by decide

/-- The group order fits in 256 bits. -/
theorem n_lt_two_pow_256 : n < 2 ^ 256 := by decide

/-- The field prime fits in 256 bits. -/
theorem p_lt_two_pow_256 : p < 2 ^ 256 := by decide

/-- `2^256 < 2p`, so a 256-bit digest is below `2p`. -/
theorem two_pow_256_lt_two_p : 2 ^ 256 < 2 * p := by decide

end StandardECDSA.Math
