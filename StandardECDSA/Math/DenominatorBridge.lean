/-
# The affine → projective denominator bridge (task G1-b)

`GoodOffset` states admissibility of the offset `H` at the level of the Mathlib
*projective* group `Grp = (params.toMathlib).toProjective.Point`, whereas every
denominator that `CompleteWitness` requires is a *field-level* statement
`x(P) - x(Q) ≠ 0` about two affine points produced by the circuit.

This module supplies the bridge between the two levels.

* `BadFamily.toAffine` / `BadFamily.avoids_toAffine` transport the bad-equation
  family along `Projective.Point.toAffineLift`, so `Avoids` can be used at the
  affine level where `Affine.Point.some` lives.
* `some_eq_or_neg_of_X_eq` is the mathematical crux: two on-curve affine points
  of P-256 with the same `x`-coordinate are equal or negatives.
* `X_eq_imp_bad` composes it with the group images `P = [a]H + B₀`,
  `Q = [b]H + B₁` of the two points, turning a vanishing denominator into one of
  three *bad equations* `[c]H = T`.
* `nsmul_ne_of_slot` and `X_ne_of_avoids` turn the absence of those equations
  from the family into `x(P) ≠ x(Q)`.
* `goodOffset_avoids_affine` / `goodOffsetAffinePt_eq_some` are the
  `GoodOffset`-level entry points.

Every proof is complete; no new axioms and no `native_decide`.
-/

import StandardECDSA.Phases.TableSemantics
import StandardECDSA.Math.OffsetConditions
import StandardECDSA.Math.SignatureEquation

namespace StandardECDSA.Math

open WeierstrassCurve StandardECDSA StandardECDSA.Gadgets StandardECDSA.Phases

/-! ## Transporting the bad family to the affine group -/

/-- `Projective.Point.toAffineLift`, as a plain function `Grp → Affine.Point Wp`. -/
noncomputable def toAff (P : Grp) : Affine.Point Wp :=
  WeierstrassCurve.Projective.Point.toAffineLift P

/-- The bad family, read in the affine group `Affine.Point Wp` instead of the
projective group `Grp`.  `Projective.Point.toAffineLift` is an additive
equivalence, so `Avoids` transports verbatim. -/
noncomputable def BadFamily.toAffine (fam : BadFamily Grp) : BadFamily (Affine.Point Wp) where
  m := fam.m
  coeff := fam.coeff
  coeff_pos := fam.coeff_pos
  coeff_lt := fam.coeff_lt
  target i := toAff (fam.target i)

@[simp] theorem BadFamily.toAffine_m (fam : BadFamily Grp) : fam.toAffine.m = fam.m := rfl

@[simp] theorem BadFamily.toAffine_coeff (fam : BadFamily Grp) (i : Fin fam.m) :
    fam.toAffine.coeff i = fam.coeff i := rfl

@[simp] theorem BadFamily.toAffine_target (fam : BadFamily Grp) (i : Fin fam.m) :
    fam.toAffine.target i = toAff (fam.target i) := rfl

/-- `toAff` commutes with `Nat`-multiples. -/
theorem toAff_nsmul (c : Nat) (P : Grp) : toAff (c • P) = c • toAff P :=
  map_nsmul (WeierstrassCurve.Projective.Point.toAffineAddEquiv params.toMathlib) c P

/-- `Avoids` transports from the projective group to the affine group. -/
theorem BadFamily.avoids_toAffine {fam : BadFamily Grp} {Hpt : Grp}
    (h : fam.Avoids Hpt) : fam.toAffine.Avoids (toAff Hpt) := by
  intro i
  have hi := h i
  show fam.coeff i • toAff Hpt ≠ toAff (fam.target i)
  rw [← toAff_nsmul]
  exact fun hc => hi ((WeierstrassCurve.Projective.Point.toAffineAddEquiv
    params.toMathlib).injective hc)

/-! ## Same `x` implies equal or opposite -/

/-- **The crux.**  Two on-curve affine points of P-256 with the same
`x`-coordinate are equal or negatives in the group. -/
theorem some_eq_or_neg_of_X_eq {x y₁ y₂ : Fp} (h₁ : NS x y₁) (h₂ : NS x y₂) :
    Affine.Point.some x y₁ h₁ = Affine.Point.some x y₂ h₂ ∨
      Affine.Point.some x y₁ h₁ = - Affine.Point.some x y₂ h₂ := by
  rcases y_eq_or_neg h₁.left h₂.left with h | h
  · left
    rw [Affine.Point.some.injEq]
    exact ⟨rfl, h⟩
  · right
    have hsome : Affine.Point.some x y₁ h₁ = Affine.Point.some x (-y₂) (negPt_ns h₂) := by
      rw [Affine.Point.some.injEq]
      exact ⟨rfl, h⟩
    rw [hsome, negPt_group x y₂ h₂]

/-! ## A vanishing denominator is a bad equation -/

/-- From `[a]H + B₀ = [b]H + B₁` and `b ≤ a`, deduce `[a-b]H = B₁ - B₀`. -/
theorem nsmul_sub_of_add_eq {G : Type} [AddCommGroup G] {Hpt B0 B1 : G} {a b : Nat}
    (h : a • Hpt + B0 = b • Hpt + B1) (hb : b ≤ a) :
    (a - b) • Hpt = B1 - B0 := by
  have ha : a = (a - b) + b := (Nat.sub_add_cancel hb).symm
  have h' : (a - b) • Hpt + b • Hpt + B0 = b • Hpt + B1 := by
    rw [← add_nsmul, ← ha]
    exact h
  have h'' : (a - b) • Hpt + B0 = B1 := by
    have h3 : b • Hpt + ((a - b) • Hpt + B0) = b • Hpt + B1 := by
      rw [← h']; abel
    exact add_left_cancel h3
  exact eq_sub_of_add_eq h''

/-- **A vanishing denominator is a bad equation.**  If two on-curve affine points
`P`, `Q` with group images `[a]H + B₀` and `[b]H + B₁` share an
`x`-coordinate, then one of the three bad equations `[a-b]H = B₁-B₀`,
`[b-a]H = B₀-B₁`, `[a+b]H = -(B₀+B₁)` holds. -/
theorem X_eq_imp_bad {xP yP xQ yQ : Fp} (hP : NS xP yP) (hQ : NS xQ yQ)
    (Hpt : Affine.Point Wp) (a b : Nat) (B0 B1 : Affine.Point Wp)
    (hPpt : Affine.Point.some xP yP hP = a • Hpt + B0)
    (hQpt : Affine.Point.some xQ yQ hQ = b • Hpt + B1)
    (hx : xP = xQ) :
    (b ≤ a ∧ (a - b) • Hpt = B1 - B0) ∨
      (a ≤ b ∧ (b - a) • Hpt = B0 - B1) ∨
      (a + b) • Hpt = -(B0 + B1) := by
  subst hx
  rcases some_eq_or_neg_of_X_eq hP hQ with h | h
  · -- `P = Q`, so `[a]H + B₀ = [b]H + B₁`
    have heq : a • Hpt + B0 = b • Hpt + B1 := by rw [← hPpt, h, hQpt]
    rcases le_total b a with hba | hab
    · exact Or.inl ⟨hba, nsmul_sub_of_add_eq heq hba⟩
    · exact Or.inr (Or.inl ⟨hab, nsmul_sub_of_add_eq heq.symm hab⟩)
  · -- `P = -Q`, so `[a]H + B₀ + ([b]H + B₁) = 0`
    right; right
    have heq : a • Hpt + B0 = -(b • Hpt + B1) := by rw [← hPpt, h, hQpt]
    have h1 : a • Hpt + B0 + (b • Hpt + B1) = 0 := by rw [heq]; abel
    have h3 : (a + b) • Hpt + (B0 + B1) = 0 := by
      rw [add_nsmul, ← h1]; abel
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using h3)

/-! ## Reading the family -/

/-- If slot `i` has coefficient `c` and target `T`, then `c • Hpt ≠ T`. -/
theorem nsmul_ne_of_slot {fam : BadFamily (Affine.Point Wp)} {Hpt : Affine.Point Wp}
    (havoid : fam.Avoids Hpt) (i : Fin fam.m) {c : Nat} (hc : fam.coeff i = c)
    {T : Affine.Point Wp} (hT : fam.target i = T) : c • Hpt ≠ T := by
  intro h
  exact havoid i (by rw [hc, hT]; exact h)

/-- **The bridge, `Avoids` form.**  If none of the three bad equations that a
vanishing denominator would produce holds, the denominator does not vanish. -/
theorem X_ne_of_avoids {xP yP xQ yQ : Fp} (hP : NS xP yP) (hQ : NS xQ yQ)
    (Hpt : Affine.Point Wp) (a b : Nat) (B0 B1 : Affine.Point Wp)
    (hPpt : Affine.Point.some xP yP hP = a • Hpt + B0)
    (hQpt : Affine.Point.some xQ yQ hQ = b • Hpt + B1)
    (h1 : ∀ c : Nat, c • Hpt = B1 - B0 → False)
    (h2 : ∀ c : Nat, c • Hpt = B0 - B1 → False)
    (h3 : ∀ c : Nat, c • Hpt = -(B0 + B1) → False) :
    xP ≠ xQ := by
  intro hx
  rcases X_eq_imp_bad hP hQ Hpt a b B0 B1 hPpt hQpt hx with ⟨_, h⟩ | ⟨_, h⟩ | h
  · exact h1 _ h
  · exact h2 _ h
  · exact h3 _ h

/-! ## The `GoodOffset` entry point -/

/-- `GoodOffset` gives the projective `Avoids` fact, unfolded. -/
theorem goodOffset_avoids (H : AffinePoint K) (hH : H.IsOnCurve params)
    {fam : BadFamily Grp} (hgood : GoodOffset H hH fam) :
    fam.Avoids (H.toProjective.toMathlibPoint params
      (affine_to_projective_on_curve H params hH)) := hgood.2

/-- `GoodOffset` gives `Z ≠ 0` for the projective lift of `H`. -/
theorem goodOffset_Z_ne (H : AffinePoint K) (hH : H.IsOnCurve params)
    {fam : BadFamily Grp} (hgood : GoodOffset H hH fam) :
    (H.toProjective).Z ≠ 0 := hgood.1

/-- The affine point of the offset `H`, as a Mathlib affine point. -/
noncomputable def goodOffsetAffinePt (H : AffinePoint K) (hH : H.IsOnCurve params) :
    Affine.Point Wp :=
  toAff (H.toProjective.toMathlibPoint params
    (affine_to_projective_on_curve H params hH))

/-- **The `GoodOffset` bridge.**  The affine-level `Avoids` fact for the offset
point `H`, which is what the honest-witness inductions consume. -/
theorem goodOffset_avoids_affine (H : AffinePoint K) (hH : H.IsOnCurve params)
    {fam : BadFamily Grp} (hgood : GoodOffset H hH fam) :
    fam.toAffine.Avoids (goodOffsetAffinePt H hH) :=
  BadFamily.avoids_toAffine (goodOffset_avoids H hH hgood)

/-- An on-curve affine point of the circuit is nonsingular. -/
theorem nsOfOnCurve (H : AffinePoint K) (hH : H.IsOnCurve params) : NS H.X H.Y := by
  have h := hH
  unfold AffinePoint.IsOnCurve at h
  exact Affine.equation_iff_nonsingular.mp (by
    rw [Affine.equation_iff]
    dsimp [Wp, AffineBridge.W, CurveParameters.toMathlib]
    linear_combination h)

/-- The affine point of the offset `H` is the `Affine.Point.some` of its
coordinates. -/
theorem goodOffsetAffinePt_eq_some (H : AffinePoint K) (hH : H.IsOnCurve params)
    {fam : BadFamily Grp} (hgood : GoodOffset H hH fam) :
    goodOffsetAffinePt H hH = Affine.Point.some H.X H.Y (nsOfOnCurve H hH) := by
  have hz : H.toProjective.toMathlib 2 ≠ 0 := by
    simp [ProjectivePoint.toMathlib, AffinePoint.toProjective]
  unfold goodOffsetAffinePt toAff
  simp only [ProjectivePoint.toMathlibPoint]
  rw [WeierstrassCurve.Projective.Point.toAffineLift_of_Z_ne_zero hz]
  rw [Affine.Point.some.injEq]
  constructor
  · show H.toProjective.toMathlib 0 / H.toProjective.toMathlib 2 = H.X
    simp [ProjectivePoint.toMathlib, AffinePoint.toProjective]
  · show H.toProjective.toMathlib 1 / H.toProjective.toMathlib 2 = H.Y
    simp [ProjectivePoint.toMathlib, AffinePoint.toProjective]

end StandardECDSA.Math
