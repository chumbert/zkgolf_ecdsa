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

/-! ## Finiteness, affine points, and the standard/signature-point equivalence

The remaining content of task T03.  The key missing ingredient is that a
projective point on the curve has `Z = 0` exactly when it is the point at
infinity; this lets the standard predicate's `V ≠ O` hypothesis produce the
affine witness `R` required by the signature-point form. -/

/-- A projective point on the curve has `Z = 0` exactly when it is the point at
infinity. -/
theorem Z_eq_zero_iff_equiv_infinity {P : ProjectivePoint K} (hP : P.IsOnCurve params) :
    P.Z = 0 ↔ ProjectiveEquiv P infinityPoint := by
  constructor
  · intro hz
    have hx := ProjectivePoint.X_eq_zero_of_Z_eq_zero P params hP hz
    have hy := ProjectivePoint.Y_ne_zero_of_Z_eq_zero P params hP hz
    refine ⟨P.Y, hy, ?_⟩
    ext <;> simp [infinityPoint, hx, hz]
  · rintro ⟨c, hc, hcP⟩
    rw [hcP, smul_projective]
    simp [infinityPoint]

/-- `ProjectiveEquiv` preserves vanishing of `Z`. -/
theorem ProjectiveEquiv.Z_eq_zero_iff {P Q : ProjectivePoint K} (h : ProjectiveEquiv P Q) :
    P.Z = 0 ↔ Q.Z = 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [smul_projective]
  simp [hc]

/-- `toMathlibPoint` does not depend on the on-curve proof. -/
theorem toMathlibPoint_proof_irrel (p : ProjectivePoint K) (h1 h2 : p.IsOnCurve params) :
    p.toMathlibPoint params h1 = p.toMathlibPoint params h2 := by
  simp only [ProjectivePoint.toMathlibPoint]

/-- The affine point with the coordinates of a finite projective point. -/
def affinePt (P : ProjectivePoint K) : AffinePoint K :=
  { X := affineX P, Y := P.Y * P.Z⁻¹ }

@[simp] theorem affinePt_X (P : ProjectivePoint K) : (affinePt P).X = affineX P := rfl

@[simp] theorem affinePt_Y (P : ProjectivePoint K) : (affinePt P).Y = P.Y * P.Z⁻¹ := rfl

/-- A finite projective point is projectively equivalent to its affine point. -/
theorem projectiveEquiv_affinePt {P : ProjectivePoint K} (hz : P.Z ≠ 0) :
    ProjectiveEquiv P (affinePt P).toProjective := by
  rw [projectiveEquiv_toProjective_iff]
  refine ⟨?_, ?_, hz⟩
  · show P.X = affineX P * P.Z
    unfold affineX
    rw [mul_assoc, inv_mul_cancel₀ hz, mul_one]
  · show P.Y = P.Y * P.Z⁻¹ * P.Z
    rw [mul_assoc, inv_mul_cancel₀ hz, mul_one]

/-- The affine point of a finite on-curve projective point is on the curve. -/
theorem affinePt_isOnCurve {P : ProjectivePoint K} (hP : P.IsOnCurve params) (hz : P.Z ≠ 0) :
    (affinePt P).IsOnCurve params := by
  obtain ⟨hx, hy, _⟩ :=
    (projectiveEquiv_toProjective_iff P (affinePt P)).mp (projectiveEquiv_affinePt hz)
  have hcurve := hP.1
  unfold ProjectivePoint.SatisfiesCurveEquation at hcurve
  rw [hx, hy, affinePt_X, affinePt_Y] at hcurve
  have hkey : ((P.Y * P.Z⁻¹) * (P.Y * P.Z⁻¹) -
      (affineX P * affineX P * affineX P + params.a * affineX P + params.b)) * P.Z ^ 3 = 0 := by
    linear_combination hcurve
  have hz3 : P.Z ^ 3 ≠ 0 := pow_ne_zero 3 hz
  have hzero := (mul_eq_zero.mp hkey).resolve_right hz3
  simp only [AffinePoint.IsOnCurve, affinePt_X, affinePt_Y]
  linear_combination hzero

/-- The Mathlib-group image of a three-term `addE` chain. -/
theorem addE3_toMathlib (A B C : ProjectivePoint K) (hA : A.IsOnCurve params)
    (hB : B.IsOnCurve params) (hC : C.IsOnCurve params)
    (h : (addE (addE A B params) C params).IsOnCurve params) :
    (addE (addE A B params) C params).toMathlibPoint params h
      = A.toMathlibPoint params hA + B.toMathlibPoint params hB + C.toMathlibPoint params hC := by
  rw [toMathlibPoint_proof_irrel _ h
    (addE_on_curve (addE A B params) C params (addE_on_curve A B params hA hB) hC)]
  rw [addE_toMathlib (addE A B params) C (addE_on_curve A B params hA hB) hC]
  rw [addE_toMathlib A B hA hB]

/-! ## The two verification points -/

/-- The standard verification point `V = [u₁]G + [u₂]Q`. -/
def stdV (Q : AffinePoint K) (r s : K) (E : Nat) : ProjectivePoint K :=
  addE (FixedTables.mulG (E * invModN s.val % n))
    (mulP (r.val * invModN s.val % n) Q.toProjective) params

/-- The circuit's three-term point `[E]G + [r]Q + [t]R`, `t = n - s`. -/
def sigW (Q : AffinePoint K) (r s : K) (E : Nat) (R : AffinePoint K) : ProjectivePoint K :=
  addE (addE (FixedTables.mulG E) (mulP r.val Q.toProjective) params)
    (mulP (n - s.val) R.toProjective) params

/-- `StandardECDSA.mulG` is the fixed-table `mulG`. -/
theorem mulG_eq_fixedTables (k : Nat) : mulG k = FixedTables.mulG k := rfl

/-- The Mathlib-group image of the public key. -/
def Qpt (Q : AffinePoint K) (hQ : Q.IsOnCurve params) : Grp :=
  Q.toProjective.toMathlibPoint params (toProjective_on_curve hQ)

/-- `stdV` is on the curve. -/
theorem stdV_on_curve (Q : AffinePoint K) (hQ : Q.IsOnCurve params) (r s : K) (E : Nat) :
    (stdV Q r s E).IsOnCurve params :=
  addE_on_curve _ _ params (FixedTables.mulG_on_curve _)
    (mulP_on_curve _ _ (toProjective_on_curve hQ))

/-- `sigW` is on the curve. -/
theorem sigW_on_curve (Q : AffinePoint K) (hQ : Q.IsOnCurve params) (r s : K) (E : Nat)
    (R : AffinePoint K) (hR : R.IsOnCurve params) :
    (sigW Q r s E R).IsOnCurve params :=
  addE_on_curve _ _ params
    (addE_on_curve _ _ params (FixedTables.mulG_on_curve _)
      (mulP_on_curve _ _ (toProjective_on_curve hQ)))
    (mulP_on_curve _ _ (toProjective_on_curve hR))

/-- `stdV` in the Mathlib group. -/
theorem stdV_toMathlib (Q : AffinePoint K) (hQ : Q.IsOnCurve params) (r s : K) (E : Nat)
    (h : (stdV Q r s E).IsOnCurve params) :
    (stdV Q r s E).toMathlibPoint params h
      = (E * invModN s.val % n) • Gpt + (r.val * invModN s.val % n) • Qpt Q hQ := by
  rw [toMathlibPoint_proof_irrel (stdV Q r s E) h
    (addE_on_curve (FixedTables.mulG (E * invModN s.val % n))
      (mulP (r.val * invModN s.val % n) Q.toProjective) params
      (FixedTables.mulG_on_curve _)
      (mulP_on_curve _ Q.toProjective (toProjective_on_curve hQ)))]
  unfold stdV
  rw [addE_toMathlib (FixedTables.mulG (E * invModN s.val % n))
      (mulP (r.val * invModN s.val % n) Q.toProjective)
      (FixedTables.mulG_on_curve _)
      (mulP_on_curve _ Q.toProjective (toProjective_on_curve hQ))]
  rw [FixedTables.mulG_toMathlib (E * invModN s.val % n),
    mulP_toMathlib (r.val * invModN s.val % n) Q.toProjective (toProjective_on_curve hQ)]
  rw [show (r.val * invModN s.val % n) % n = r.val * invModN s.val % n from Nat.mod_mod _ n]
  simp only [Qpt]

/-- `sigW` in the Mathlib group. -/
theorem sigW_toMathlib (Q : AffinePoint K) (hQ : Q.IsOnCurve params) (r s : K) (E : Nat)
    (R : AffinePoint K) (hR : R.IsOnCurve params)
    (hrn : r.val < n) (hs0 : 0 < s.val)
    (h : (sigW Q r s E R).IsOnCurve params) :
    (sigW Q r s E R).toMathlibPoint params h
      = E • Gpt + r.val • Qpt Q hQ
        + (n - s.val) • R.toProjective.toMathlibPoint params (toProjective_on_curve hR) := by
  rw [toMathlibPoint_proof_irrel (sigW Q r s E R) h
    (addE_on_curve (addE (FixedTables.mulG E) (mulP r.val Q.toProjective) params)
      (mulP (n - s.val) R.toProjective) params
      (addE_on_curve (FixedTables.mulG E) (mulP r.val Q.toProjective) params
        (FixedTables.mulG_on_curve E)
        (mulP_on_curve _ Q.toProjective (toProjective_on_curve hQ)))
      (mulP_on_curve _ R.toProjective (toProjective_on_curve hR)))]
  unfold sigW
  rw [addE3_toMathlib (FixedTables.mulG E) (mulP r.val Q.toProjective)
    (mulP (n - s.val) R.toProjective)
    (FixedTables.mulG_on_curve E) (mulP_on_curve _ Q.toProjective (toProjective_on_curve hQ))
    (mulP_on_curve _ R.toProjective (toProjective_on_curve hR))]
  rw [FixedTables.mulG_toMathlib E,
    mulP_toMathlib r.val Q.toProjective (toProjective_on_curve hQ),
    mulP_toMathlib (n - s.val) R.toProjective (toProjective_on_curve hR)]
  rw [Nat.mod_eq_of_lt hrn, Nat.mod_eq_of_lt (by omega : n - s.val < n)]
  simp only [Qpt]

/-- **The standard predicate is the signature-point predicate** (core form).

Both predicates share the hypotheses `Q.IsOnCurve`, `0 < r < n`, `0 < s < n`;
this lemma relates the remaining conjuncts. -/
theorem standard_core_iff (Q : AffinePoint K) (hQ : Q.IsOnCurve params)
    {r s : K} (hr0 : 0 < r.val) (hrn : r.val < n) (hs0 : 0 < s.val) (hsn : s.val < n)
    (E : Nat) :
    (¬ ProjectiveEquiv (stdV Q r s E) infinityPoint ∧ (affineX (stdV Q r s E)).val % n = r.val)
    ↔
    (∃ R : AffinePoint K, R.IsOnCurve params ∧
      ProjectiveEquiv (sigW Q r s E R) infinityPoint ∧ R.X.val % n = r.val) := by
  have hsw : s.val * invModN s.val % n = 1 := s_mul_invModN s.val hs0 hsn
  have hV_on : (stdV Q r s E).IsOnCurve params := stdV_on_curve Q hQ r s E
  have hVpt : (stdV Q r s E).toMathlibPoint params hV_on
      = (E * invModN s.val % n) • Gpt + (r.val * invModN s.val % n) • Qpt Q hQ :=
    stdV_toMathlib Q hQ r s E hV_on
  constructor
  · rintro ⟨hVne, hx⟩
    have hVz : (stdV Q r s E).Z ≠ 0 := fun hz =>
      hVne ((Z_eq_zero_iff_equiv_infinity hV_on).mp hz)
    have hR_on : (affinePt (stdV Q r s E)).IsOnCurve params := affinePt_isOnCurve hV_on hVz
    have hRp_on : (affinePt (stdV Q r s E)).toProjective.IsOnCurve params :=
      toProjective_on_curve hR_on
    have hVeq : ProjectiveEquiv (stdV Q r s E) (affinePt (stdV Q r s E)).toProjective :=
      projectiveEquiv_affinePt hVz
    have hVeq_pt : (stdV Q r s E).toMathlibPoint params hV_on
        = (affinePt (stdV Q r s E)).toProjective.toMathlibPoint params hRp_on :=
      (projectiveEquiv_iff_toMathlib (stdV Q r s E) (affinePt (stdV Q r s E)).toProjective
        hV_on hRp_on).mp hVeq
    have hRpt_eq : (affinePt (stdV Q r s E)).toProjective.toMathlibPoint params hRp_on
        = (E * invModN s.val % n) • Gpt + (r.val * invModN s.val % n) • Qpt Q hQ := by
      rw [← hVpt]
      exact hVeq_pt.symm
    have hW_on : (sigW Q r s E (affinePt (stdV Q r s E))).IsOnCurve params :=
      sigW_on_curve Q hQ r s E _ hR_on
    have hWpt : (sigW Q r s E (affinePt (stdV Q r s E))).toMathlibPoint params hW_on
        = E • Gpt + r.val • Qpt Q hQ
          + (n - s.val) • (affinePt (stdV Q r s E)).toProjective.toMathlibPoint params hRp_on :=
      sigW_toMathlib Q hQ r s E _ hR_on hrn hs0 hW_on
    have hzero : E • Gpt + r.val • Qpt Q hQ
        + (n - s.val) • (affinePt (stdV Q r s E)).toProjective.toMathlibPoint params hRp_on = 0 :=
      (signature_equation_iff (E := E) (r := r.val) (s := s.val) (w := invModN s.val)
        (u1 := E * invModN s.val % n) (u2 := r.val * invModN s.val % n) (t := n - s.val)
        hs0 hsn hsw rfl rfl rfl Gpt (Qpt Q hQ) _).mpr hRpt_eq
    refine ⟨affinePt (stdV Q r s E), hR_on, ?_, ?_⟩
    · rw [projectiveEquiv_iff_toMathlib (sigW Q r s E (affinePt (stdV Q r s E))) infinityPoint
        hW_on (infinity_on_curve params), infinity_toMathlib, hWpt, hzero]
    · show (affineX (stdV Q r s E)).val % n = r.val
      exact hx
  · rintro ⟨R, hR, heq, hRx⟩
    have hRp_on : R.toProjective.IsOnCurve params := toProjective_on_curve hR
    have hRpZ : R.toProjective.Z = 1 := rfl
    have hW_on : (sigW Q r s E R).IsOnCurve params := sigW_on_curve Q hQ r s E R hR
    have hWpt : (sigW Q r s E R).toMathlibPoint params hW_on
        = E • Gpt + r.val • Qpt Q hQ
          + (n - s.val) • R.toProjective.toMathlibPoint params hRp_on :=
      sigW_toMathlib Q hQ r s E R hR hrn hs0 hW_on
    have heq' : (sigW Q r s E R).toMathlibPoint params hW_on = 0 := by
      rw [projectiveEquiv_iff_toMathlib (sigW Q r s E R) infinityPoint hW_on
        (infinity_on_curve params), infinity_toMathlib] at heq
      exact heq
    have hzero : E • Gpt + r.val • Qpt Q hQ
        + (n - s.val) • R.toProjective.toMathlibPoint params hRp_on = 0 := by
      rw [← hWpt]
      exact heq'
    have hRpt_eq : R.toProjective.toMathlibPoint params hRp_on
        = (E * invModN s.val % n) • Gpt + (r.val * invModN s.val % n) • Qpt Q hQ :=
      (signature_equation_iff (E := E) (r := r.val) (s := s.val) (w := invModN s.val)
        (u1 := E * invModN s.val % n) (u2 := r.val * invModN s.val % n) (t := n - s.val)
        hs0 hsn hsw rfl rfl rfl Gpt (Qpt Q hQ) _).mp hzero
    have hVeq_pt : (stdV Q r s E).toMathlibPoint params hV_on
        = R.toProjective.toMathlibPoint params hRp_on := by
      rw [hVpt, hRpt_eq]
    have hVeq : ProjectiveEquiv (stdV Q r s E) R.toProjective :=
      (projectiveEquiv_iff_toMathlib (stdV Q r s E) R.toProjective hV_on hRp_on).mpr hVeq_pt
    have hVz : (stdV Q r s E).Z ≠ 0 := by
      intro hz
      have h1 : R.toProjective.Z = 0 := (ProjectiveEquiv.Z_eq_zero_iff hVeq).mp hz
      rw [hRpZ] at h1
      exact one_ne_zero h1
    refine ⟨?_, ?_⟩
    · intro h
      exact hVz ((Z_eq_zero_iff_equiv_infinity hV_on).mpr h)
    · rw [affineX_eq_of_projectiveEquiv hVeq]
      exact hRx

/-- **The standard predicate is the signature-point predicate** (task T03).

`standardVerify` (textbook `V = [u₁]G + [u₂]Q`, `V ≠ O`, `val(x(V)) mod n = r`)
holds exactly when there is a finite on-curve point `R` with
`[E]G + [r]Q + [t]R = O` (`t = n - s`) and `val(R.x) mod n = r`. -/
theorem standard_iff_signaturePoint (pkX pkY digestLo digestHi r s : K) :
    standardVerify pkX pkY digestLo digestHi r s ↔
      signaturePointVerify pkX pkY digestLo digestHi r s := by
  simp only [standardVerify, signaturePointVerify, Digest.toNat]
  constructor
  · rintro ⟨hQ, hr0, hrn, hs0, hsn, hrest⟩
    exact ⟨hQ, hr0, hrn, hs0, hsn,
      (standard_core_iff _ hQ hr0 hrn hs0 hsn _).mp hrest⟩
  · rintro ⟨hQ, hr0, hrn, hs0, hsn, hrest⟩
    exact ⟨hQ, hr0, hrn, hs0, hsn,
      (standard_core_iff _ hQ hr0 hrn hs0 hsn _).mpr hrest⟩

end StandardECDSA.Math
