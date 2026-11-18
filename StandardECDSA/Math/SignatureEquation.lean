/-
# The signature equation (task T03)

The circuit proves the *signature-point* form of verification: there is a finite
on-curve point `R` with

```text
[E]G + [r]Q + [t]R = O,      t = n - s,      val(R.x) mod n = r.
```

The standard predicate instead computes `V = [u₁]G + [u₂]Q` with
`u₁ = E·s⁻¹ mod n`, `u₂ = r·s⁻¹ mod n`, and requires `V ≠ O` and
`val(x(V)) mod n = r`.

This module proves the two forms equivalent.  The group-theoretic content is
that `V = R`:

* `[s]V = [E]G + [r]Q`, because `s·u₁ ≡ E` and `s·u₂ ≡ r (mod n)`;
* `[s]R = [E]G + [r]Q`, because `[t]R = -[s]R` and the circuit equation gives
  `[t]R = -([E]G + [r]Q)`;
* `[s]` is injective on the P-256 group since `0 < s < n` and `n` is prime.

Everything is stated in the concrete Mathlib group
`(params.toMathlib).toProjective.Point`, whose order is `n`
(`Math/GroupOrder.lean`).  No subgroup, candidate-injectivity or curve-order
hypothesis remains.
-/

import StandardECDSA.Math.FixedTables
import StandardECDSA.Math.GroupOrder
import StandardECDSA.Spec

namespace StandardECDSA.Math

open StandardECDSA

set_option maxRecDepth 100000

/-- The P-256 group, as a Mathlib abelian group. -/
abbrev Grp := (params.toMathlib).toProjective.Point

/-! ## Group-level scalar arithmetic -/

/-- In a group of exponent `n`, `[n - s]P = -[s]P`. -/
theorem nsub_nsmul {s : Nat} (hs : s ≤ n) (P : Grp) : (n - s) • P = -(s • P) := by
  have h : s • P + (n - s) • P = 0 := by
    rw [← add_nsmul, Nat.add_sub_cancel' hs, nsmul_eq_zero]
  exact eq_neg_of_add_eq_zero_right h

/-- `[a]P = [b]P` when `a ≡ b (mod n)`. -/
theorem nsmul_mod_congr {a b : Nat} (h : a % n = b % n) (P : Grp) : a • P = b • P := by
  have ha : a • P = (a % n) • P := by
    conv_lhs => rw [show a = n * (a / n) + a % n from (Nat.div_add_mod a n).symm]
    rw [add_nsmul, mul_nsmul, nsmul_eq_zero, nsmul_zero, zero_add]
  have hb : b • P = (b % n) • P := by
    conv_lhs => rw [show b = n * (b / n) + b % n from (Nat.div_add_mod b n).symm]
    rw [add_nsmul, mul_nsmul, nsmul_eq_zero, nsmul_zero, zero_add]
  rw [ha, hb, h]

/-- `Nat`-scalar distributivity over `+` on the P-256 group.

Proved by induction because the group's `SMul ℕ` instance is `NSMul.toSMul`
rather than a `DistribSMul`, so `smul_add` does not apply. -/
theorem nsmul_add' (s : Nat) (x y : Grp) : s • (x + y) = s • x + s • y := by
  induction s with
  | zero => simp
  | succ k ih => rw [succ_nsmul, ih, succ_nsmul, succ_nsmul]; abel

/-- `Nat`-scalar distributivity over `-` on the P-256 group. -/
theorem nsmul_sub' (s : Nat) (x y : Grp) : s • (x - y) = s • x - s • y := by
  induction s with
  | zero => simp
  | succ k ih => rw [succ_nsmul, ih, succ_nsmul, succ_nsmul]; abel

/-- `Nat`-scalar commutation with negation on the P-256 group. -/
theorem nsmul_neg' (s : Nat) (x : Grp) : s • (-x) = -(s • x) := by
  induction s with
  | zero => simp
  | succ k ih => rw [succ_nsmul, ih, succ_nsmul]; abel

/-- `s · (E · w) ≡ E (mod n)` when `s · w ≡ 1 (mod n)`. -/
theorem mul_inv_mod_left {E s w : Nat} (hsw : s * w % n = 1) :
    (s * (E * w)) % n = E % n := by
  have h1 : s * (E * w) = E * (s * w) := by ring
  have h2 : (E * (s * w)) % n = E % n * ((s * w) % n) % n := Nat.mul_mod ..
  rw [h1, h2, hsw, Nat.mul_one, Nat.mod_mod]

/-! ## The signature equation -/

/-- **The signature equation (group level).**

With `0 < s < n`, `w = s⁻¹ mod n`, `u₁ = E·w mod n`, `u₂ = r·w mod n` and
`t = n - s`, the circuit equation `[E]G + [r]Q + [t]R = O` holds exactly when
`R = [u₁]G + [u₂]Q`. -/
theorem signature_equation_iff {E r s w u1 u2 t : Nat}
    (hs0 : 0 < s) (hsn : s < n)
    (hsw : s * w % n = 1)
    (hu1 : u1 = E * w % n) (hu2 : u2 = r * w % n) (ht : t = n - s)
    (G Q R : Grp) :
    E • G + r • Q + t • R = 0 ↔ R = u1 • G + u2 • Q := by
  have hsu1 : (s * u1) % n = E % n := by
    have h2 : (s * u1) % n = s % n * (u1 % n) % n := Nat.mul_mod ..
    rw [h2, hu1, Nat.mod_mod, ← Nat.mul_mod]
    exact mul_inv_mod_left hsw
  have hsu2 : (s * u2) % n = r % n := by
    have h2 : (s * u2) % n = s % n * (u2 % n) % n := Nat.mul_mod ..
    rw [h2, hu2, Nat.mod_mod, ← Nat.mul_mod]
    exact mul_inv_mod_left hsw
  have hV : s • (u1 • G + u2 • Q) = E • G + r • Q := by
    have h1 : s • (u1 • G + u2 • Q) = s • (u1 • G) + s • (u2 • Q) := nsmul_add' s _ _
    have h2 : s • (u1 • G) = (s * u1) • G := smul_smul s u1 G
    have h3 : s • (u2 • Q) = (s * u2) • Q := smul_smul s u2 Q
    have h4 : (s * u1) • G = E • G := nsmul_mod_congr hsu1 G
    have h5 : (s * u2) • Q = r • Q := nsmul_mod_congr hsu2 Q
    rw [h1, h2, h3, h4, h5]
  constructor
  · intro h
    have htR : t • R = -(E • G + r • Q) := by
      have h' : (E • G + r • Q) + t • R = 0 := h
      calc t • R = 0 - (E • G + r • Q) := by rw [← h']; abel
        _ = -(E • G + r • Q) := by abel
    have htR2 : t • R = -(s • (u1 • G + u2 • Q)) := by rw [htR, hV]
    have htR3 : t • R = -(s • R) := by rw [ht]; exact nsub_nsmul (le_of_lt hsn) R
    have hsRV : s • R = s • (u1 • G + u2 • Q) := by
      have hneg : -(s • R) = -(s • (u1 • G + u2 • Q)) := by rw [← htR3, htR2]
      exact neg_injective hneg
    have hzero : s • (R - (u1 • G + u2 • Q)) = 0 := by
      have h1 : s • (R - (u1 • G + u2 • Q)) = s • R - s • (u1 • G + u2 • Q) :=
        nsmul_sub' s _ _
      rw [h1, hsRV, sub_self]
    have hinj := nsmul_injective_of_lt s hs0 hsn
    have hX : R - (u1 • G + u2 • Q) = 0 := by
      have h0 : s • (R - (u1 • G + u2 • Q)) = s • (0 : Grp) := by rw [hzero, nsmul_zero]
      exact hinj h0
    exact sub_eq_zero.mp hX
  · intro h
    have htR : t • R = -(E • G + r • Q) := by
      rw [h, ht, nsub_nsmul (le_of_lt hsn), hV]
    rw [htR]
    abel

/-! ## The `x`-coordinate lift -/

/-- **The `x`-coordinate lift.**

For `0 < r < n` and a Boolean `overflow` with `r + n·overflow < p`, the field
element `r + n·overflow` has canonical natural value `r + n·overflow` and
reduces to `r` modulo `n`.  This is the arithmetic content of the circuit's
`rx = r + n·overflow` branch: the lift never wraps modulo `p`, and the reduced
`x`-coordinate is exactly `r`. -/
theorem x_mod_order_iff_lift {r overflow : Nat} (hr : r < n)
    (_ho : overflow = 0 ∨ overflow = 1) (hp : r + n * overflow < p) :
    (((r + n * overflow : Nat) : K).val = r + n * overflow) ∧
      ((((r + n * overflow : Nat) : K).val) % n = r) := by
  have h1 : (((r + n * overflow : Nat) : K).val) = (r + n * overflow) % p :=
    ZMod.val_natCast _ _
  rw [h1, Nat.mod_eq_of_lt hp]
  refine ⟨rfl, ?_⟩
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hr

/-! ## Bridges to the Mathlib group

These are the plumbing lemmas that let the concrete `standardVerify` /
`signaturePointVerify` predicates be rewritten in the Mathlib group.  They are
all transported from the vendored kernel-checked `ECBridge` lemmas. -/

/-- `s · (s⁻¹ mod n) ≡ 1 (mod n)` for `0 < s < n`. -/
theorem s_mul_invModN (s : Nat) (hs0 : 0 < s) (hsn : s < n) : s * invModN s % n = 1 := by
  have hne : (s : ZMod n) ≠ 0 := by
    refine (ZMod.val_ne_zero _).mp ?_
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hsn]
    omega
  have h1 : (s : ZMod n) * ((s : ZMod n))⁻¹ = 1 := mul_inv_cancel₀ hne
  have h2 : ((s : ZMod n) * ((s : ZMod n))⁻¹).val = (1 : ZMod n).val := by rw [h1]
  rw [ZMod.val_mul, ZMod.val_natCast, ZMod.val_one] at h2
  rw [Nat.mod_eq_of_lt hsn] at h2
  exact h2

/-- The projective lift of an affine on-curve point is on the curve. -/
theorem toProjective_on_curve {Q : AffinePoint K} (hQ : Q.IsOnCurve params) :
    Q.toProjective.IsOnCurve params := by
  refine ⟨?_, ?_⟩
  · unfold ProjectivePoint.SatisfiesCurveEquation AffinePoint.IsOnCurve at *
    simp only
    linear_combination hQ
  · intro h
    have hz := congr_arg ProjectivePoint.Z h
    simp [infinityPoint] at hz

/-- `mulP k P` is on the curve. -/
theorem mulP_on_curve (k : Nat) (P : ProjectivePoint K) (hP : P.IsOnCurve params) :
    (mulP k P).IsOnCurve params :=
  bsmul_on_curve _ P params hP

/-- `mulP k P` in the Mathlib group is `[k]P`. -/
theorem mulP_toMathlib (k : Nat) (P : ProjectivePoint K) (hP : P.IsOnCurve params) :
    (mulP k P).toMathlibPoint params (mulP_on_curve k P hP) =
      (k % n) • P.toMathlibPoint params hP := by
  have h := toMathlibPoint_bsmul (padBits (natToBits (k % n)) 256) P params hP
  rw [bitsToNat_padBits] at h
  exact h

/-- `addE` in the Mathlib group is the group sum. -/
theorem addE_toMathlib (P Q : ProjectivePoint K) (hP : P.IsOnCurve params)
    (hQ : Q.IsOnCurve params) :
    (addE P Q params).toMathlibPoint params (addE_on_curve P Q params hP hQ) =
      P.toMathlibPoint params hP + Q.toMathlibPoint params hQ :=
  toMathlibPoint_add P Q params hP hQ

/-- `ProjectiveEquiv` is equality in the Mathlib group. -/
theorem projectiveEquiv_iff_toMathlib (P Q : ProjectivePoint K)
    (hP : P.IsOnCurve params) (hQ : Q.IsOnCurve params) :
    ProjectiveEquiv P Q ↔ P.toMathlibPoint params hP = Q.toMathlibPoint params hQ :=
  (toMathlibPoint_eq_iff_ProjectiveEquiv P Q params hP hQ).symm

/-- The point at infinity is `0` in the Mathlib group. -/
theorem infinity_toMathlib :
    infinityPoint.toMathlibPoint params (infinity_on_curve params) = 0 :=
  toMathlibPoint_infinity params _

/-- The affine `x`-coordinate of a projectively equivalent point. -/
theorem affineX_eq_of_projectiveEquiv {P : ProjectivePoint K} {R : AffinePoint K}
    (h : ProjectiveEquiv P R.toProjective) : affineX P = R.X := by
  obtain ⟨hx, _, hz⟩ := projectiveEquiv_toProjective_iff P R |>.mp h
  unfold affineX
  rw [hx, mul_assoc, mul_inv_cancel₀ hz, mul_one]

/-- The affine `y`-coordinate of a projectively equivalent point. -/
theorem affineY_eq_of_projectiveEquiv {P : ProjectivePoint K} {R : AffinePoint K}
    (h : ProjectiveEquiv P R.toProjective) : P.Y * P.Z⁻¹ = R.Y := by
  obtain ⟨_, hy, hz⟩ := projectiveEquiv_toProjective_iff P R |>.mp h
  rw [hy, mul_assoc, mul_inv_cancel₀ hz, mul_one]

end StandardECDSA.Math
