import Baseline.Projected.ProjectiveBridge
import Baseline.Projected.P256Bridge
import Challenge.Specs.ECDSAP256Projected

/-! Group-form specification of the projected-signature relation, and its
equivalence with the trusted `Challenge.Specs.ECDSAP256Projected.Spec`. -/
namespace Solution.Projected

set_option maxHeartbeats 1600000

open Challenge.Specs.ECDSAP256
open WeierstrassCurve

abbrev W := params.toMathlib.toAffine

/-- Affine point of the mathlib group law from a curve equation. -/
def pt (x y : K) (h : y^2 = x^3 + params.a*x + params.b) : W.Point :=
  Affine.Point.some x y (Baseline.Projected.AffineBridge.short_nonsingular params x y h)

lemma generator_eq : params.gy^2 = params.gx^3 + params.a*params.gx + params.b := by
  decide

abbrev G : W.Point := pt params.gx params.gy generator_eq

/-- Projective lift of an affine point. -/
abbrev proj (x y : K) : ProjectivePoint K := ({ X := x, Y := y } : AffinePoint K).toProjective

/-- Group-form specification: the ECDSA verification equation in the mathlib
group law, with the four precomputation sums nonzero. -/
def GroupSpec (pkX pkY digest r s : K) : Prop :=
  ∃ (E t : ℕ) (ry : K)
    (hQ : pkY^2 = pkX^3 + params.a*pkX + params.b)
    (hR : ry^2 = r^3 + params.a*r + params.b),
    E < 2^256 ∧ (E : K) = digest ∧ r.val < n ∧ t < n ∧ n - t = s.val ∧
    r ≠ 0 ∧ (t : K) ≠ 0 ∧ pkX ≠ 0 ∧
    G + pt pkX pkY hQ ≠ 0 ∧ pt r ry hR + G ≠ 0 ∧
    pt r ry hR + pt pkX pkY hQ ≠ 0 ∧ G + (pt r ry hR + pt pkX pkY hQ) ≠ 0 ∧
    E • G + r.val • pt pkX pkY hQ + t • pt r ry hR = 0

/-! ## Bridge lemmas -/

lemma infinity_on_curve : infinityPoint.IsOnCurve params := by
  refine ⟨?_, ?_⟩
  · unfold ProjectivePoint.SatisfiesCurveEquation infinityPoint; simp
  · intro h; have := congrArg ProjectivePoint.Y h; simpa [infinityPoint] using this

lemma proj_on_curve (x y : K) (h : y^2 = x^3 + params.a*x + params.b) :
    (proj x y).IsOnCurve params :=
  affine_to_projective_on_curve _ params (by
    show y*y = x*x*x + params.a*x + params.b
    linear_combination h)

lemma proj_toMathlibPoint (x y : K) (h : y^2 = x^3 + params.a*x + params.b) :
    (proj x y).toMathlibPoint params (proj_on_curve x y h) = (pt x y h).toProjective :=
  Baseline.Projected.AffineBridge.liftAffine_fromAffine params x y h

/-- The `X = 0 ∧ Z = 0` infinity test is equivalent to vanishing in mathlib's group. -/
lemma infinity_iff_toMathlibPoint_zero (P : ProjectivePoint K) (hP : P.IsOnCurve params) :
    (P.X = 0 ∧ P.Z = 0) ↔ P.toMathlibPoint params hP = 0 := by
  have hEquiv : (P.X = 0 ∧ P.Z = 0) ↔ ProjectiveEquiv P infinityPoint := by
    constructor
    · rintro ⟨hx, hz⟩
      have hY : P.Y ≠ 0 := by
        intro hy
        exact hP.2 (by ext <;> simp [hx, hy, hz])
      refine ⟨P.Y, hY, ?_⟩
      have hsm : (P.Y • infinityPoint : ProjectivePoint K) = { X := P.Y * 0, Y := P.Y * 1, Z := P.Y * 0 } := rfl
      rw [hsm]
      apply ProjectivePoint.ext
      · rw [hx]; simp
      · simp
      · rw [hz]; simp
    · rintro ⟨c, hc, h⟩
      have hx : P.X = 0 := by rw [h]; simp [infinityPoint]
      have hz : P.Z = 0 := by rw [h]; simp [infinityPoint]
      exact ⟨hx, hz⟩
  rw [hEquiv]
  constructor
  · intro h
    rw [← toMathlibPoint_infinity params infinity_on_curve]
    exact (toMathlibPoint_eq_iff_ProjectiveEquiv P infinityPoint params hP infinity_on_curve).mpr h
  · intro h
    exact (toMathlibPoint_eq_iff_ProjectiveEquiv P infinityPoint params hP infinity_on_curve).mp
      (by rw [h, toMathlibPoint_infinity params infinity_on_curve])

/-- A sum is affine (Z ≠ 0) iff it is nonzero in mathlib's group. -/
lemma addE_Z_ne_zero_iff (A B : ProjectivePoint K) (hA : A.IsOnCurve params) (hB : B.IsOnCurve params) :
    (addE A B params).Z ≠ 0 ↔ A.toMathlibPoint params hA + B.toMathlibPoint params hB ≠ 0 := by
  have hsum := addE_on_curve A B params hA hB
  have hadd := toMathlibPoint_add A B params hA hB
  constructor
  · intro hz hzero
    apply hz
    have hE : ProjectiveEquiv (addE A B params) infinityPoint :=
      (toMathlibPoint_eq_iff_ProjectiveEquiv _ infinityPoint params hsum infinity_on_curve).mp
        (by rw [hadd, hzero, toMathlibPoint_infinity params infinity_on_curve])
    exact (RepresentationBridge.projective_infinity_test_iff _ infinityPoint hE).mpr
      ⟨rfl, rfl⟩ |>.2
  · intro hne hz
    apply hne
    rw [← hadd]
    have hx : (addE A B params).X = 0 := by
      have h_eq := hsum.1
      unfold ProjectivePoint.SatisfiesCurveEquation at h_eq
      rw [hz] at h_eq
      have h3 : (0:K) = (addE A B params).X * ((addE A B params).X * (addE A B params).X) := by
        linear_combination h_eq
      rcases mul_eq_zero.mp h3.symm with h | h
      · exact h
      · rcases mul_eq_zero.mp h with h | h
        · exact h
        · exact h
    have hY : (addE A B params).Y ≠ 0 := by
      intro hy
      exact hsum.2 (by ext <;> simp [hx, hy, hz])
    have hE : ProjectiveEquiv (addE A B params) infinityPoint := ⟨(addE A B params).Y, hY, by
      have hsm : ((addE A B params).Y • infinityPoint : ProjectivePoint K) =
          { X := (addE A B params).Y * 0, Y := (addE A B params).Y * 1, Z := (addE A B params).Y * 0 } := rfl
      rw [hsm]
      apply ProjectivePoint.ext
      · rw [hx]; simp
      · simp
      · rw [hz]; simp⟩
    exact ((toMathlibPoint_eq_iff_ProjectiveEquiv _ infinityPoint params hsum infinity_on_curve).mpr hE).trans
      (toMathlibPoint_infinity params infinity_on_curve)

set_option maxHeartbeats 3200000 in
/-- Wrapper with the on-curve proof as a variable, so `rw`/`simp only` can match. -/
lemma toMathlibPoint_add' (A B : ProjectivePoint K) (hA : A.IsOnCurve params) (hB : B.IsOnCurve params)
    (h : (addE A B params).IsOnCurve params) :
    (addE A B params).toMathlibPoint params h = A.toMathlibPoint params hA + B.toMathlibPoint params hB :=
  toMathlibPoint_add A B params hA hB

/-- Wrapper with the on-curve proof as a variable. -/
lemma toMathlibPoint_bsmul' (s : List Bool) (P : ProjectivePoint K) (hP : P.IsOnCurve params)
    (h : (bsmul s P params).IsOnCurve params) :
    (bsmul s P params).toMathlibPoint params h = bitsToNat s • P.toMathlibPoint params hP :=
  toMathlibPoint_bsmul s P params hP

/-- The scalar combination's infinity test is the ECDSA group equation. -/
lemma scalarCombination_iff (pkX pkY r ry : K) (E t : ℕ)
    (hQ : pkY^2 = pkX^3 + params.a*pkX + params.b)
    (hR : ry^2 = r^3 + params.a*r + params.b) :
    (RepresentationBridge.ScalarCombination ⟨pkX, pkY⟩ E r.val t ry params).X = 0 ∧
    (RepresentationBridge.ScalarCombination ⟨pkX, pkY⟩ E r.val t ry params).Z = 0 ↔
    E • G + r.val • pt pkX pkY hQ + t • pt r ry hR = 0 := by
  have hReq : ry^2 = (r.val : K)^3 + params.a*(r.val : K) + params.b := by
    rw [ZMod.natCast_zmod_val r]; exact hR
  have hG := proj_on_curve params.gx params.gy generator_eq
  have hQ' := proj_on_curve pkX pkY hQ
  have hR' := proj_on_curve (r.val : K) ry hReq
  have heG : (bsmul (padBits (natToBits E) params.kBits) (proj params.gx params.gy) params).IsOnCurve params :=
    bsmul_on_curve _ _ params hG
  have hrQ : (bsmul (padBits (natToBits r.val) params.kBits) (proj pkX pkY) params).IsOnCurve params :=
    bsmul_on_curve _ _ params hQ'
  have htR : (bsmul (padBits (natToBits t) params.kBits) (proj (r.val : K) ry) params).IsOnCurve params :=
    bsmul_on_curve _ _ params hR'
  have hSC : (RepresentationBridge.ScalarCombination ⟨pkX, pkY⟩ E r.val t ry params).IsOnCurve params := by
    unfold RepresentationBridge.ScalarCombination
    exact addE_on_curve _ _ params (addE_on_curve _ _ params heG hrQ) htR
  have hSCadd : (RepresentationBridge.ScalarCombination ⟨pkX, pkY⟩ E r.val t ry params).toMathlibPoint params hSC =
      (bsmul (padBits (natToBits E) params.kBits) (proj params.gx params.gy) params).toMathlibPoint params heG +
      (bsmul (padBits (natToBits r.val) params.kBits) (proj pkX pkY) params).toMathlibPoint params hrQ +
      (bsmul (padBits (natToBits t) params.kBits) (proj (r.val : K) ry) params).toMathlibPoint params htR := by
    unfold RepresentationBridge.ScalarCombination
    exact (toMathlibPoint_add _ _ params (addE_on_curve _ _ params heG hrQ) htR).trans
      (congrArg (· + (bsmul (padBits (natToBits t) params.kBits) (proj (r.val : K) ry) params).toMathlibPoint params htR)
        (toMathlibPoint_add _ _ params heG hrQ))
  have hE : (bsmul (padBits (natToBits E) params.kBits) (proj params.gx params.gy) params).toMathlibPoint params heG =
      E • G.toProjective := by
    rw [show (bsmul (padBits (natToBits E) params.kBits) (proj params.gx params.gy) params).toMathlibPoint params heG =
        bitsToNat (padBits (natToBits E) params.kBits) • (proj params.gx params.gy).toMathlibPoint params hG
      from toMathlibPoint_bsmul _ _ params hG, bitsToNat_padBits, proj_toMathlibPoint params.gx params.gy generator_eq]
  have hr : (bsmul (padBits (natToBits r.val) params.kBits) (proj pkX pkY) params).toMathlibPoint params hrQ =
      r.val • (pt pkX pkY hQ).toProjective := by
    rw [show (bsmul (padBits (natToBits r.val) params.kBits) (proj pkX pkY) params).toMathlibPoint params hrQ =
        bitsToNat (padBits (natToBits r.val) params.kBits) • (proj pkX pkY).toMathlibPoint params hQ'
      from toMathlibPoint_bsmul _ _ params hQ', bitsToNat_padBits, proj_toMathlibPoint pkX pkY hQ]
  have ht : (bsmul (padBits (natToBits t) params.kBits) (proj (r.val : K) ry) params).toMathlibPoint params htR =
      t • (pt (r.val : K) ry hReq).toProjective := by
    rw [show (bsmul (padBits (natToBits t) params.kBits) (proj (r.val : K) ry) params).toMathlibPoint params htR =
        bitsToNat (padBits (natToBits t) params.kBits) • (proj (r.val : K) ry).toMathlibPoint params hR'
      from toMathlibPoint_bsmul _ _ params hR', bitsToNat_padBits, proj_toMathlibPoint (r.val : K) ry hReq]
  have toProj_add (a b : W.Point) : (a + b).toProjective = a.toProjective + b.toProjective :=
    map_add (Projective.Point.toAffineAddEquiv params.toMathlib.toProjective).symm a b
  have toProj_nsmul (m : ℕ) (a : W.Point) : (m • a).toProjective = m • a.toProjective :=
    map_nsmul (Projective.Point.toAffineAddEquiv params.toMathlib.toProjective).symm m a
  have toProj_inj : Function.Injective (Affine.Point.toProjective : W.Point → _) :=
    (Projective.Point.toAffineAddEquiv params.toMathlib.toProjective).symm.injective
  have hsum : (RepresentationBridge.ScalarCombination ⟨pkX, pkY⟩ E r.val t ry params).toMathlibPoint params hSC =
      (E • G + r.val • pt pkX pkY hQ + t • pt (r.val : K) ry hReq).toProjective := by
    rw [hSCadd, hE, hr, ht, toProj_add, toProj_add, toProj_nsmul, toProj_nsmul, toProj_nsmul]
  rw [infinity_iff_toMathlibPoint_zero _ hSC, hsum]
  simp only [ZMod.natCast_zmod_val]
  exact ⟨fun h => toProj_inj h, fun h => by rw [h]; exact Projective.Point.fromAffine_zero⟩

/-- Affine normalization of a projective point with nonzero Z. -/
def normPt (P : ProjectivePoint K) : ProjectivePoint K :=
  { X := P.X * P.Z⁻¹, Y := P.Y * P.Z⁻¹, Z := 1 }

lemma normPt_eq (P : ProjectivePoint K) :
    normPt P = ({ X := P.X * P.Z⁻¹, Y := P.Y * P.Z⁻¹ } : AffinePoint K).toProjective := rfl

/-- Generic bridge: the Z ≠ 0 test of `addE A' (normPt (addE A B))` is
nonvanishing of the mathlib sum. -/
lemma addE_norm_Z_iff (A' A B : ProjectivePoint K) (hA' : A'.IsOnCurve params)
    (hA : A.IsOnCurve params) (hB : B.IsOnCurve params)
    (hz : (addE A B params).Z ≠ 0) :
    (addE A' (normPt (addE A B params)) params).Z ≠ 0 ↔
      A'.toMathlibPoint params hA' + (A.toMathlibPoint params hA + B.toMathlibPoint params hB) ≠ 0 := by
  have hAB := addE_on_curve A B params hA hB
  have hnorm : (normPt (addE A B params)).IsOnCurve params := by
    rw [normPt_eq]
    exact projective_point_on_curve_of_point_equality _ _ _ params hAB hz
      ⟨by rw [mul_comm (addE A B params).X (addE A B params).Z⁻¹, ← mul_assoc, mul_inv_cancel₀ hz, one_mul],
        by rw [mul_comm (addE A B params).Y (addE A B params).Z⁻¹, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]⟩
  rw [addE_Z_ne_zero_iff A' _ hA' hnorm]
  have hval : (normPt (addE A B params)).toMathlibPoint params hnorm
      = (addE A B params).toMathlibPoint params hAB :=
    (toMathlibPoint_eq_iff_ProjectiveEquiv _ _ params hnorm hAB).mpr
      (projective_equiv_of_point_equality _ _ _ hz
        ⟨by rw [mul_comm (addE A B params).X (addE A B params).Z⁻¹, ← mul_assoc, mul_inv_cancel₀ hz, one_mul],
          by rw [mul_comm (addE A B params).Y (addE A B params).Z⁻¹, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]⟩)
  rw [hval, toMathlibPoint_add' A B hA hB hAB]

/-- The four precomputation sums are nonzero iff the corresponding group sums are nonzero. -/
lemma originalFiniteSums_iff (pkX pkY r ry : K)
    (hQ : pkY^2 = pkX^3 + params.a*pkX + params.b)
    (hR : ry^2 = r^3 + params.a*r + params.b) :
    RepresentationBridge.OriginalFiniteSums ⟨pkX, pkY⟩ r ry params ↔
      G + pt pkX pkY hQ ≠ 0 ∧ pt r ry hR + G ≠ 0 ∧
      pt r ry hR + pt pkX pkY hQ ≠ 0 ∧ G + (pt r ry hR + pt pkX pkY hQ) ≠ 0 := by
  have hG := proj_on_curve params.gx params.gy generator_eq
  have hQ' := proj_on_curve pkX pkY hQ
  have hR' := proj_on_curve r ry hR
  have hRQon : (addE (proj r ry) (proj pkX pkY) params).IsOnCurve params :=
    addE_on_curve _ _ params hR' hQ'
  have toProj_add (a b : W.Point) : (a + b).toProjective = a.toProjective + b.toProjective :=
    map_add (Projective.Point.toAffineAddEquiv params.toMathlib.toProjective).symm a b
  have hinj := (Projective.Point.toAffineAddEquiv params.toMathlib.toProjective).symm.injective
  have nz {a b : W.Point} : a.toProjective + b.toProjective ≠ 0 ↔ a + b ≠ 0 := by
    constructor
    · intro h h0; apply h; rw [← toProj_add, h0]; exact Projective.Point.fromAffine_zero
    · intro h h0; apply h
      exact hinj (by rw [← toProj_add] at h0; exact h0.trans Projective.Point.fromAffine_zero.symm)
  have nz' {a b : W.Point} : (a + b).toProjective ≠ 0 ↔ a + b ≠ 0 := by
    rw [toProj_add]; exact nz
  have gGQ : (proj params.gx params.gy).toMathlibPoint params hG + (proj pkX pkY).toMathlibPoint params hQ' =
      (G + pt pkX pkY hQ).toProjective := by
    rw [proj_toMathlibPoint params.gx params.gy generator_eq, proj_toMathlibPoint pkX pkY hQ, toProj_add]
  have gRG : (proj r ry).toMathlibPoint params hR' + (proj params.gx params.gy).toMathlibPoint params hG =
      (pt r ry hR + G).toProjective := by
    rw [proj_toMathlibPoint r ry hR, proj_toMathlibPoint params.gx params.gy generator_eq, toProj_add]
  have gRQ : (proj r ry).toMathlibPoint params hR' + (proj pkX pkY).toMathlibPoint params hQ' =
      (pt r ry hR + pt pkX pkY hQ).toProjective := by
    rw [proj_toMathlibPoint r ry hR, proj_toMathlibPoint pkX pkY hQ, toProj_add]
  have gGRQ : (proj params.gx params.gy).toMathlibPoint params hG +
      (pt r ry hR + pt pkX pkY hQ).toProjective =
      (G + (pt r ry hR + pt pkX pkY hQ)).toProjective := by
    rw [proj_toMathlibPoint params.gx params.gy generator_eq]
    exact (toProj_add _ _).symm
  have e1 := addE_Z_ne_zero_iff (proj params.gx params.gy) (proj pkX pkY) hG hQ'
  have e2 := addE_Z_ne_zero_iff (proj r ry) (proj params.gx params.gy) hR' hG
  have e3 := addE_Z_ne_zero_iff (proj r ry) (proj pkX pkY) hR' hQ'
  have e4 := addE_norm_Z_iff (proj params.gx params.gy) (proj r ry) (proj pkX pkY) hG hR' hQ'
  simp only [RepresentationBridge.OriginalFiniteSums, normPt_eq]
  constructor
  · rintro ⟨c1, c2, c3, c4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact nz'.mp (by rw [← gGQ]; exact e1.mp c1)
    · exact nz'.mp (by rw [← gRG]; exact e2.mp c2)
    · exact nz'.mp (by rw [← gRQ]; exact e3.mp c3)
    · have h4 := (e4 c3).mp c4
      rw [gRQ, gGRQ] at h4
      exact nz'.mp h4
  · rintro ⟨g1, g2, g3, g4⟩
    have c3 : (addE (proj r ry) (proj pkX pkY) params).Z ≠ 0 := e3.mpr (by rw [gRQ]; exact nz'.mpr g3)
    refine ⟨?_, ?_, c3, ?_⟩
    · exact e1.mpr (by rw [gGQ]; exact nz'.mpr g1)
    · exact e2.mpr (by rw [gRG]; exact nz'.mpr g2)
    · have h4 : (proj params.gx params.gy).toMathlibPoint params hG +
          ((proj r ry).toMathlibPoint params hR' + (proj pkX pkY).toMathlibPoint params hQ') ≠ 0 := by
        rw [gRQ, gGRQ]
        exact nz'.mpr g4
      exact (e4 c3).mpr h4

/-- The trusted projected spec is equivalent to the group-form spec. -/
theorem spec_iff_groupSpec (pkX pkY digest r s : K) :
    Challenge.Specs.ECDSAP256Projected.Spec pkX pkY digest r s ↔ GroupSpec pkX pkY digest r s := by
  have hspec : Challenge.Specs.ECDSAP256Projected.Spec pkX pkY digest r s =
      RepresentationBridge.BoundLF ⟨pkX, pkY⟩ digest r.val s.val n params := rfl
  rw [hspec, RepresentationBridge.P256.p256_boundLF_iff_representation_independent]
  constructor
  · rintro ⟨E, t, ry, hE, he, hr, ht, hs, hpk, hR, hrnz, htnz, hpkz, hfin, hx, hz⟩
    have hQ : pkY^2 = pkX^3 + params.a*pkX + params.b := by
      dsimp only [AffinePoint.IsOnCurve] at hpk; linear_combination hpk
    have hR' : ry^2 = r^3 + params.a*r + params.b := by
      dsimp only [AffinePoint.IsOnCurve] at hR; simp only [ZMod.natCast_zmod_val] at hR; linear_combination hR
    have hrnz' : r ≠ 0 := by simpa only [ZMod.natCast_zmod_val] using hrnz
    simp only [ZMod.natCast_zmod_val] at hfin
    refine ⟨E, t, ry, hQ, hR', hE, he, hr, ht, hs, hrnz', htnz, hpkz, ?_, ?_, ?_, ?_, ?_⟩
    · exact ((originalFiniteSums_iff pkX pkY r ry hQ hR').mp hfin).1
    · exact ((originalFiniteSums_iff pkX pkY r ry hQ hR').mp hfin).2.1
    · exact ((originalFiniteSums_iff pkX pkY r ry hQ hR').mp hfin).2.2.1
    · exact ((originalFiniteSums_iff pkX pkY r ry hQ hR').mp hfin).2.2.2
    · exact (scalarCombination_iff pkX pkY r ry E t hQ hR').mp ⟨hx, hz⟩
  · rintro ⟨E, t, ry, hQ, hR', hE, he, hr, ht, hs, hrnz, htnz, hpkz, hfin1, hfin2, hfin3, hfin4, hcomb⟩
    have hfin : G + pt pkX pkY hQ ≠ 0 ∧ pt r ry hR' + G ≠ 0 ∧
        pt r ry hR' + pt pkX pkY hQ ≠ 0 ∧ G + (pt r ry hR' + pt pkX pkY hQ) ≠ 0 :=
      ⟨hfin1, hfin2, hfin3, hfin4⟩
    have hQon : AffinePoint.IsOnCurve ⟨pkX, pkY⟩ params := by
      dsimp only [AffinePoint.IsOnCurve]; linear_combination hQ
    refine ⟨E, t, ry, hE, he, hr, ht, hs, hQon, ?_, ?_, ?_, hpkz, ?_, ?_⟩
    · dsimp only [AffinePoint.IsOnCurve]; simp only [ZMod.natCast_zmod_val]; linear_combination hR'
    · rw [ZMod.natCast_zmod_val r]; exact hrnz
    · exact htnz
    · simp only [ZMod.natCast_zmod_val]
      exact (originalFiniteSums_iff pkX pkY r ry hQ hR').mpr hfin
    · exact (scalarCombination_iff pkX pkY r ry E t hQ hR').mpr hcomb

end Solution.Projected

#print axioms Solution.Projected.spec_iff_groupSpec
