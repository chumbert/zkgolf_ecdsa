/-
# P-256 group order certification

This module certifies that the P-256 group order `n` is prime, that the
generator has order exactly `n`, and that the whole group has cardinality `n`.
The last step is the Hasse-free argument of the plan (section 5):

1. `n` is prime (kernel-checked Pratt certificate, `ECDSA.P256OrderPratt`);
2. `[n]G = O` and `G ≠ O`, so `addOrderOf G = n`;
3. hence `n ∣ N` where `N` is the group cardinality (Lagrange);
4. `N ≤ 2p + 1` (at most two `y` per `x`, plus the point at infinity);
5. `N` is odd (a point of order two would be a root of `x³ + a·x + b`);
6. `2p + 1 < 3n`, so `N ∈ {n, 2n}`, and `N` odd forces `N = n`.

No subgroup, cardinality or curve-order hypothesis remains.
-/

import StandardECDSA.Math.P256
import ECDSA.ECBridge
import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Fintype.Card
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

namespace StandardECDSA.Math

open StandardECDSA

set_option maxRecDepth 100000
set_option exponentiation.threshold 400

/-! ## Instances for the Mathlib bridge -/

instance : NeZero (2 : K) := ⟨by decide⟩
instance : NeZero (3 : K) := ⟨by decide⟩

instance : (params.toMathlib).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  decide

instance : CurveHasNoPointsOfOrder2 params := ⟨no_two_torsion⟩

/-! ## Primality of the group order -/

/-- The P-256 group order `n` is prime.  Kernel-checked Pratt certificate. -/
theorem n_prime : Nat.Prime n :=
  ECDSA.prime_115792089210356248762697446949407573529996955224135760342422259061068512044369

instance : Fact (Nat.Prime n) := ⟨n_prime⟩

/-! ## The generator has order `n` -/

/-- `[n]G = O` in the vendored projective representation. -/
theorem bsmul_n_gPoint :
    ProjectiveEquiv (bsmul (padBits (natToBits n) 256) gPoint params) infinityPoint := by
  have hx : (bsmul (padBits (natToBits n) 256) gPoint params).X = 0 := by decide
  have hz : (bsmul (padBits (natToBits n) 256) gPoint params).Z = 0 := by decide
  have hy : (bsmul (padBits (natToBits n) 256) gPoint params).Y ≠ 0 := by decide
  refine ⟨(bsmul (padBits (natToBits n) 256) gPoint params).Y, hy, ?_⟩
  ext <;> simp [infinityPoint, hx, hz]

/-- The generator as a Mathlib projective point. -/
noncomputable def Gpt : (params.toMathlib).toProjective.Point :=
  gPoint.toMathlibPoint params gPoint_on_curve

/-- `n • G = 0` in the Mathlib group. -/
theorem nsmul_n_Gpt : n • Gpt = 0 := by
  have h := toMathlibPoint_bsmul (padBits (natToBits n) 256) gPoint params gPoint_on_curve
  rw [bitsToNat_padBits] at h
  rw [show Gpt = gPoint.toMathlibPoint params gPoint_on_curve from rfl, ← h]
  rw [(toMathlibPoint_eq_iff_ProjectiveEquiv _ infinityPoint params
    (bsmul_on_curve _ _ _ gPoint_on_curve) (infinity_on_curve params)).mpr bsmul_n_gPoint]
  exact toMathlibPoint_infinity params (infinity_on_curve params)

/-- The generator is not the identity. -/
theorem Gpt_ne_zero : Gpt ≠ 0 := by
  intro h
  have h2 : gPoint.toMathlibPoint params gPoint_on_curve = 0 := by
    rw [show gPoint.toMathlibPoint params gPoint_on_curve = Gpt from rfl, h]
  have h3 : infinityPoint.toMathlibPoint params (infinity_on_curve params) = 0 :=
    toMathlibPoint_infinity params (infinity_on_curve params)
  have h_equiv := (toMathlibPoint_eq_iff_ProjectiveEquiv gPoint infinityPoint params
    gPoint_on_curve (infinity_on_curve params)).mp (h2.trans h3.symm)
  rcases h_equiv with ⟨c, _, hc⟩
  have hz := congr_arg ProjectivePoint.Z hc
  simp [gPoint, infinityPoint] at hz

/-- The generator has additive order exactly `n`. -/
theorem addOrderOf_Gpt : addOrderOf Gpt = n :=
  addOrderOf_eq_prime nsmul_n_Gpt Gpt_ne_zero

/-- `n` divides the group cardinality. -/
theorem n_dvd_card : n ∣ Nat.card (params.toMathlib).toProjective.Point := by
  rw [← addOrderOf_Gpt]
  exact addOrderOf_dvd_natCard Gpt


/-! ## Cardinality of the P-256 group

The plan's Hasse-free route: at most two `y` per `x` plus the point at infinity,
so `N ≤ 2p + 1`; `N` is odd because a point of order two would be a root of the
cubic; `n ∣ N`; and `2p + 1 < 3n` forces `N = n`.
-/

/-- The affine point type of the P-256 curve. -/
abbrev APt : Type := WeierstrassCurve.Affine.Point params.toMathlib

/-- The affine Weierstrass equation of P-256 in explicit form. -/
theorem equation_iff' {x y : K} :
    WeierstrassCurve.Affine.Equation params.toMathlib x y ↔ y ^ 2 = x ^ 3 + params.a * x + params.b := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [CurveParameters.toMathlib]
  constructor <;> intro h <;> linear_combination h

/-- Two points with the same `x`-coordinate have equal or opposite `y`-coordinates. -/
theorem y_eq_or_neg {x y₁ y₂ : K}
    (h₁ : WeierstrassCurve.Affine.Equation params.toMathlib x y₁) (h₂ : WeierstrassCurve.Affine.Equation params.toMathlib x y₂) :
    y₁ = y₂ ∨ y₁ = -y₂ := by
  have e₁ := equation_iff'.mp h₁
  have e₂ := equation_iff'.mp h₂
  have h : (y₁ - y₂) * (y₁ + y₂) = 0 := by linear_combination e₁ - e₂
  rcases mul_eq_zero.mp h with h | h
  · left; linear_combination h
  · right; linear_combination h

/-- A canonical `y`-coordinate for a given `x`, when one exists. -/
noncomputable def yCanon (x : K) : K := by
  classical
  exact if h : ∃ y, WeierstrassCurve.Affine.Equation params.toMathlib x y then Classical.choose h else 0

theorem yCanon_spec {x : K} (h : ∃ y, WeierstrassCurve.Affine.Equation params.toMathlib x y) :
    WeierstrassCurve.Affine.Equation params.toMathlib x (yCanon x) := by
  unfold yCanon
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem eq_yCanon_or_neg {x y : K} (h : WeierstrassCurve.Affine.Equation params.toMathlib x y) :
    y = yCanon x ∨ y = -yCanon x :=
  y_eq_or_neg h (yCanon_spec ⟨y, h⟩)

/-- Code an affine point as `none` (the point at infinity) or `(x, sign)`, where the
sign records whether `y` is the canonical representative of its `x`-fibre. -/
noncomputable def toCode : APt → Option (Fin p × Bool)
  | .zero => none
  | .some x y _ => some (⟨x.val, ZMod.val_lt x⟩, decide (y = yCanon x))

theorem toCode_injective : Function.Injective toCode := by
  intro P Q h
  cases P with
  | zero =>
      cases Q with
      | zero => rfl
      | some x y hns => simp [toCode] at h
  | some x y hns =>
      cases Q with
      | zero => simp [toCode] at h
      | some x' y' hns' =>
          simp only [toCode, Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq] at h
          obtain ⟨hx, hb⟩ := h
          have hx' : x = x' := ZMod.val_injective p hx
          subst hx'
          have hiff : (y = yCanon x) ↔ (y' = yCanon x) := by
            constructor
            · intro hp
              have h1 : decide (y = yCanon x) = true := by rw [hp]; simp
              rw [h1] at hb
              exact of_decide_eq_true hb.symm
            · intro hq
              have h1 : decide (y' = yCanon x) = true := by rw [hq]; simp
              rw [h1] at hb
              exact of_decide_eq_true hb
          have hy : y = y' := by
            by_cases hc : y = yCanon x
            · rw [hc, hiff.mp hc]
            · have hc' : y' ≠ yCanon x := fun hh => hc (hiff.mpr hh)
              rcases eq_yCanon_or_neg (x := x) hns.left with h1 | h1
              · exact absurd h1 hc
              · rcases eq_yCanon_or_neg (x := x) hns'.left with h2 | h2
                · exact absurd h2 hc'
                · rw [h1, h2]
          subst hy
          exact congrArg (WeierstrassCurve.Affine.Point.some x y) (Subsingleton.elim hns hns')

/-- At most `2p + 1` affine points: `p` choices of `x`, two signs, plus infinity. -/
theorem card_affine_le : Nat.card APt ≤ 2 * p + 1 := by
  have h := Nat.card_le_card_of_injective toCode toCode_injective
  have hopt : Nat.card (Option (Fin p × Bool)) = 2 * p + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool]
    ring
  rwa [hopt] at h

/-- The projective and affine point types have the same cardinality. -/
theorem card_projective_eq_affine :
    Nat.card (params.toMathlib).toProjective.Point = Nat.card APt :=
  Nat.card_congr (WeierstrassCurve.Projective.Point.toAffineAddEquiv _).toEquiv

/-- The group cardinality is odd: a point of order two would give a root of the cubic. -/
theorem card_odd : Odd (Nat.card (params.toMathlib).toProjective.Point) := by
  rw [card_projective_eq_affine]
  by_contra hodd
  haveI : Finite APt := Finite.of_injective toCode toCode_injective
  have hmod : Nat.card APt % 2 = 0 := Nat.not_odd_iff.mp hodd
  have h2dvd : 2 ∣ Nat.card APt := Nat.dvd_of_mod_eq_zero hmod
  obtain ⟨P, hP⟩ := exists_prime_addOrderOf_dvd_card' 2 h2dvd
  have hPP : P + P = 0 := by
    have h := addOrderOf_nsmul_eq_zero P
    rw [hP] at h
    simpa [two_nsmul] using h
  have hPne : P ≠ 0 := by
    intro h
    rw [h, addOrderOf_zero] at hP
    exact absurd hP (by norm_num)
  cases P with
  | zero => exact hPne rfl
  | some x y hns =>
      have hroot := WeierstrassCurve.Affine.Point.isRoot_twoTorsionPolynomial_of_add_self hns hPP
      rw [Polynomial.IsRoot.def, WeierstrassCurve.eval_toPoly_twoTorsionPolynomial] at hroot
      simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
        CurveParameters.toMathlib] at hroot
      have h4 : (4 : K) ≠ 0 := by decide
      have hzero : x ^ 3 + params.a * x + params.b = 0 := by
        have hh : (4 : K) * (x ^ 3 + params.a * x + params.b) = 0 := by linear_combination hroot
        exact (mul_eq_zero.mp hh).resolve_left h4
      exact no_two_torsion x hzero

/-- The P-256 group has exactly `n` points. -/
theorem card_eq_n : Nat.card (params.toMathlib).toProjective.Point = n := by
  have hdvd := n_dvd_card
  have hle : Nat.card (params.toMathlib).toProjective.Point ≤ 2 * p + 1 := by
    rw [card_projective_eq_affine]; exact card_affine_le
  haveI : Finite APt := Finite.of_injective toCode toCode_injective
  haveI : Finite (params.toMathlib).toProjective.Point :=
    Finite.of_equiv APt (WeierstrassCurve.Projective.Point.toAffineAddEquiv _).toEquiv.symm
  have hpos : 0 < Nat.card (params.toMathlib).toProjective.Point :=
    Nat.card_pos_iff.mpr ⟨⟨0⟩, inferInstance⟩
  obtain ⟨k, hk⟩ := hdvd
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, Nat.mul_zero] at hk; omega
    · exact h
  have hk3 : k < 3 := by
    by_contra h
    push_neg at h
    have h1 : n * k ≤ 2 * p + 1 := by rw [← hk]; exact hle
    have h2 : 2 * p + 1 < 3 * n := two_p_plus_one_lt_three_n
    have h3 : n * 3 ≤ n * k := Nat.mul_le_mul_left n h
    rw [mul_comm n 3] at h3
    omega
  have hk1 : k = 1 ∨ k = 2 := by omega
  rcases hk1 with h | h
  · rw [h, Nat.mul_one] at hk; exact hk
  · exfalso
    have hodd := card_odd
    rw [hk, h] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_two_mul n)

/-! ## Consequences: `n`-torsion and small-multiplier injectivity -/

/-- Every point of the P-256 group is killed by `n`. -/
theorem nsmul_eq_zero (P : (params.toMathlib).toProjective.Point) : n • P = 0 := by
  have h : addOrderOf P ∣ n := by
    rw [← card_eq_n]
    exact addOrderOf_dvd_natCard P
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mp h

/-- `[n]P = O` for every curve point, in the vendored projective representation. -/
theorem nsmul_order_eq_zero (P : ProjectivePoint K) (hP : P.IsOnCurve params) :
    ProjectiveEquiv (bsmul (padBits (natToBits n) 256) P params) infinityPoint := by
  have h := toMathlibPoint_bsmul (padBits (natToBits n) 256) P params hP
  rw [bitsToNat_padBits] at h
  rw [nsmul_eq_zero] at h
  have h_inf : infinityPoint.toMathlibPoint params (infinity_on_curve params) = 0 :=
    toMathlibPoint_infinity params (infinity_on_curve params)
  refine (toMathlibPoint_eq_iff_ProjectiveEquiv _ infinityPoint params
    (bsmul_on_curve _ _ _ hP) (infinity_on_curve params)).mp ?_
  rw [h, h_inf]

/-- Multiplication by `k` with `0 < k < n` is injective on the P-256 group. -/
theorem nsmul_injective_of_lt (k : Nat) (hk0 : 0 < k) (hkn : k < n) :
    Function.Injective (fun P : (params.toMathlib).toProjective.Point => k • P) := by
  intro P Q h
  have h' : k • P = k • Q := h
  have hzero : k • (P - Q) = 0 := by rw [nsmul_sub, h', sub_self]
  have hdvd : addOrderOf (P - Q) ∣ k := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hzero
  have hdvd' : addOrderOf (P - Q) ∣ n := by
    rw [← card_eq_n]; exact addOrderOf_dvd_natCard _
  have hcop : k.Coprime n := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd n_prime).mpr (by
      intro hd
      have := Nat.le_of_dvd hk0 hd
      omega)
  have h1 : addOrderOf (P - Q) ∣ 1 := by
    have hg := Nat.dvd_gcd hdvd hdvd'
    rwa [Nat.coprime_iff_gcd_eq_one.mp hcop] at hg
  have h2 : addOrderOf (P - Q) = 1 := Nat.dvd_one.mp h1
  have h3 : P - Q = 0 := by
    have hh := addOrderOf_nsmul_eq_zero (P - Q)
    rw [h2] at hh
    simpa using hh
  exact sub_eq_zero.mp h3

end StandardECDSA.Math
