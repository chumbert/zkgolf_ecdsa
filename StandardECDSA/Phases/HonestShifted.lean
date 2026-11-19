/-
# Honest-witness denominators (task G1-c, shifted-table part)

`CompleteWitness` (`StandardECDSA/Main.lean`) carries the five shifted-table
denominators `hs1 … hs5` as explicit hypotheses.  This module discharges them
from `GoodOffset`, using the corrected `sh` slot group of
`StandardECDSA/Math/OffsetFamily.lean` (see FINDING 3 there).

The five denominators are

| name | denominator | wire |
|---|---|---|
| `hs1` | `x(H) - x(2H)` | `off7 + 2` |
| `hs2` | `x(Q) - x(3H)` | `off7 + 6` |
| `hs3` | `x(R) - x(3H)` | `off7 + 6` |
| `hs4` | `x(R) - x(3H+Q)` | `off7 + 10` |
| `hs5` | `x(R) - x(-3H+Q)` | `off7 + 22` |

Each is proved by `X_ne_of_avoids_sharp` with the two bad equations read off the
matching `sh` slot pair.  `hs5` needs one extra step: the wire holds
`-3H + Q = -(3H - Q)`, and negation preserves the `x`-coordinate, so the two bad
equations are `[3]H = Q - R` and `[3]H = Q + R` — exactly the corrected
`k = 4` slots.

Every proof is complete; no new axioms and no `native_decide`.
-/

import StandardECDSA.Phases.HonestDenominators

namespace StandardECDSA.Phases

open WeierstrassCurve StandardECDSA StandardECDSA.Gadgets StandardECDSA.Math
open StandardECDSA.Math.FixedTables

/-! ## The ten `sh` slot targets, in affine form -/

/-- `toAff` sends the projective infinity to the affine one. -/
theorem toAff_zero : toAff (0 : Grp) = 0 := by
  simp only [toAff, WeierstrassCurve.Projective.Point.toAffineLift_zero]

/-- The affine target of the `sh` slot `(k, s)`, unfolded. -/
theorem famOf_target_sh (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) (k : Fin 5) (s : Bool) :
    (famOf env eb rb sb Qpt Rpt).toAffine.target
        (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl (k, s))))))
      = (if k.val = 0 then 0
          else if k.val = 1 then (if s then -Qpt else Qpt)
          else if k.val = 2 then (if s then -Rpt else Rpt)
          else if k.val = 3 then (if s then -Rpt + -Qpt else Rpt + -Qpt)
          else (if s then Qpt + Rpt else Qpt + -Rpt)) := by
  show toAff ((famOf env eb rb sb Qpt Rpt).target
    (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl (k, s))))))) = _
  rw [famOf_target_apply]
  simp only [targetOf]
  split_ifs <;> simp only [toAff_toProjective, toAff_zero]

/-- The `sh` slot `(0, false)`: `[1]H = 0`. -/
theorem famOf_target_sh0f (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) :
    (famOf env eb rb sb Qpt Rpt).toAffine.target
        (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((0 : Fin 5), false))))))
      = 0 := by
  rw [famOf_target_sh]
  norm_num

/-- The `sh` slot `(0, true)`: `[3]H = 0`. -/
theorem famOf_target_sh0t (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) :
    (famOf env eb rb sb Qpt Rpt).toAffine.target
        (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((0 : Fin 5), true))))))
      = 0 := by
  rw [famOf_target_sh]
  norm_num

/-- The `sh` slot `(1, false)`: `[3]H = Q`. -/
theorem famOf_target_sh1f (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) :
    (famOf env eb rb sb Qpt Rpt).toAffine.target
        (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((1 : Fin 5), false))))))
      = Qpt := by
  rw [famOf_target_sh]
  norm_num

/-- The `sh` slot `(1, true)`: `[3]H = -Q`. -/
theorem famOf_target_sh1t (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) :
    (famOf env eb rb sb Qpt Rpt).toAffine.target
        (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((1 : Fin 5), true))))))
      = -Qpt := by
  rw [famOf_target_sh]
  norm_num

/-- The `sh` slot `(2, false)`: `[3]H = R`. -/
theorem famOf_target_sh2f (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) :
    (famOf env eb rb sb Qpt Rpt).toAffine.target
        (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((2 : Fin 5), false))))))
      = Rpt := by
  rw [famOf_target_sh]
  norm_num

/-- The `sh` slot `(2, true)`: `[3]H = -R`. -/
theorem famOf_target_sh2t (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) :
    (famOf env eb rb sb Qpt Rpt).toAffine.target
        (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((2 : Fin 5), true))))))
      = -Rpt := by
  rw [famOf_target_sh]
  norm_num

/-- The `sh` slot `(3, false)`: `[3]H = R - Q`. -/
theorem famOf_target_sh3f (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) :
    (famOf env eb rb sb Qpt Rpt).toAffine.target
        (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((3 : Fin 5), false))))))
      = Rpt + -Qpt := by
  rw [famOf_target_sh]
  norm_num

/-- The `sh` slot `(3, true)`: `[3]H = -R - Q`. -/
theorem famOf_target_sh3t (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) :
    (famOf env eb rb sb Qpt Rpt).toAffine.target
        (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((3 : Fin 5), true))))))
      = -Rpt + -Qpt := by
  rw [famOf_target_sh]
  norm_num

/-- The `sh` slot `(4, false)`: `[3]H = Q - R`. -/
theorem famOf_target_sh4f (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) :
    (famOf env eb rb sb Qpt Rpt).toAffine.target
        (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((4 : Fin 5), false))))))
      = Qpt + -Rpt := by
  rw [famOf_target_sh]
  norm_num

/-- The `sh` slot `(4, true)`: `[3]H = Q + R`. -/
theorem famOf_target_sh4t (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) :
    (famOf env eb rb sb Qpt Rpt).toAffine.target
        (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((4 : Fin 5), true))))))
      = Qpt + Rpt := by
  rw [famOf_target_sh]
  norm_num

/-! ## The five denominators -/

/-- `hs1`: `x(H) ≠ x(2H)`. -/
theorem hs1_dx (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) (H : AffinePoint K) (hH : H.IsOnCurve params)
    (hgood : GoodOffset H hH (famOf env eb rb sb Qpt Rpt))
    (x2 y2 : Fp) (h2ns : NS x2 y2)
    (h2pt : Affine.Point.some x2 y2 h2ns = 2 • goodOffsetAffinePt H hH) :
    H.X - x2 ≠ 0 := by
  classical
  have havoid := famOf_avoids_affine env eb rb sb Qpt Rpt H hH hgood
  have hHpt : goodOffsetAffinePt H hH = Affine.Point.some H.X H.Y (nsOfOnCurve H hH) :=
    goodOffsetAffinePt_eq_some H hH hgood
  have hc0 : (famOf env eb rb sb Qpt Rpt).toAffine.coeff
      (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((0 : Fin 5), false)))))) = 1 := by
    simp only [famOf_coeff_apply]
    rfl
  have hc1 : (famOf env eb rb sb Qpt Rpt).toAffine.coeff
      (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((0 : Fin 5), true)))))) = 3 := by
    simp only [famOf_coeff_apply]
    rfl
  have hA := nsmul_ne_of_slot havoid _ hc0 (T := (0 : Affine.Point Wp))
    (famOf_target_sh0f env eb rb sb Qpt Rpt)
  have hB := nsmul_ne_of_slot havoid _ hc1 (T := (0 : Affine.Point Wp))
    (famOf_target_sh0t env eb rb sb Qpt Rpt)
  have h2 : (2 - 1) • goodOffsetAffinePt H hH ≠ (0 : Affine.Point Wp) - 0 := by
    simpa using hA
  have h3 : (1 + 2) • goodOffsetAffinePt H hH ≠ -((0 : Affine.Point Wp) + 0) := by
    simpa using hB
  have hne := X_ne_of_avoids_sharp (nsOfOnCurve H hH) h2ns (goodOffsetAffinePt H hH) 1 2 0 0
    (by rw [hHpt]; simp)
    (by rw [h2pt]; simp)
    (by omega) (fun _ => h2) h3
  exact sub_ne_zero.mpr hne

/-- `hs2`: `x(Q) ≠ x(3H)`. -/
theorem hs2_dx (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) (H : AffinePoint K) (hH : H.IsOnCurve params)
    (hgood : GoodOffset H hH (famOf env eb rb sb Qpt Rpt))
    (qx qy : Fp) (hq : NS qx qy) (hQpt : Qpt = Affine.Point.some qx qy hq)
    (x3 y3 : Fp) (h3ns : NS x3 y3)
    (h3pt : Affine.Point.some x3 y3 h3ns = 3 • goodOffsetAffinePt H hH) :
    qx - x3 ≠ 0 := by
  classical
  have havoid := famOf_avoids_affine env eb rb sb Qpt Rpt H hH hgood
  have hc0 : (famOf env eb rb sb Qpt Rpt).toAffine.coeff
      (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((1 : Fin 5), false)))))) = 3 := by
    simp only [famOf_coeff_apply]
    rfl
  have hc1 : (famOf env eb rb sb Qpt Rpt).toAffine.coeff
      (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((1 : Fin 5), true)))))) = 3 := by
    simp only [famOf_coeff_apply]
    rfl
  have hA := nsmul_ne_of_slot havoid _ hc0 (T := Qpt)
    (famOf_target_sh1f env eb rb sb Qpt Rpt)
  have hB := nsmul_ne_of_slot havoid _ hc1 (T := -Qpt)
    (famOf_target_sh1t env eb rb sb Qpt Rpt)
  have h2 : (3 - 0) • goodOffsetAffinePt H hH ≠ Qpt - 0 := by
    simpa using hA
  have h3 : (0 + 3) • goodOffsetAffinePt H hH ≠ -(Qpt + 0) := by
    simpa using hB
  have hne := X_ne_of_avoids_sharp hq h3ns (goodOffsetAffinePt H hH) 0 3 Qpt 0
    (by rw [hQpt]; simp)
    (by rw [h3pt]; simp)
    (by omega) (fun _ => h2) h3
  exact sub_ne_zero.mpr hne

/-- `hs3`: `x(R) ≠ x(3H)`. -/
theorem hs3_dx (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) (H : AffinePoint K) (hH : H.IsOnCurve params)
    (hgood : GoodOffset H hH (famOf env eb rb sb Qpt Rpt))
    (rx ry : Fp) (hr : NS rx ry) (hRpt : Rpt = Affine.Point.some rx ry hr)
    (x3 y3 : Fp) (h3ns : NS x3 y3)
    (h3pt : Affine.Point.some x3 y3 h3ns = 3 • goodOffsetAffinePt H hH) :
    rx - x3 ≠ 0 := by
  classical
  have havoid := famOf_avoids_affine env eb rb sb Qpt Rpt H hH hgood
  have hc0 : (famOf env eb rb sb Qpt Rpt).toAffine.coeff
      (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((2 : Fin 5), false)))))) = 3 := by
    simp only [famOf_coeff_apply]
    rfl
  have hc1 : (famOf env eb rb sb Qpt Rpt).toAffine.coeff
      (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((2 : Fin 5), true)))))) = 3 := by
    simp only [famOf_coeff_apply]
    rfl
  have hA := nsmul_ne_of_slot havoid _ hc0 (T := Rpt)
    (famOf_target_sh2f env eb rb sb Qpt Rpt)
  have hB := nsmul_ne_of_slot havoid _ hc1 (T := -Rpt)
    (famOf_target_sh2t env eb rb sb Qpt Rpt)
  have h2 : (3 - 0) • goodOffsetAffinePt H hH ≠ Rpt - 0 := by
    simpa using hA
  have h3 : (0 + 3) • goodOffsetAffinePt H hH ≠ -(Rpt + 0) := by
    simpa using hB
  have hne := X_ne_of_avoids_sharp hr h3ns (goodOffsetAffinePt H hH) 0 3 Rpt 0
    (by rw [hRpt]; simp)
    (by rw [h3pt]; simp)
    (by omega) (fun _ => h2) h3
  exact sub_ne_zero.mpr hne

/-- `hs4`: `x(R) ≠ x(3H + Q)`. -/
theorem hs4_dx (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) (H : AffinePoint K) (hH : H.IsOnCurve params)
    (hgood : GoodOffset H hH (famOf env eb rb sb Qpt Rpt))
    (rx ry : Fp) (hr : NS rx ry) (hRpt : Rpt = Affine.Point.some rx ry hr)
    (x4 y4 : Fp) (h4ns : NS x4 y4)
    (h4pt : Affine.Point.some x4 y4 h4ns = 3 • goodOffsetAffinePt H hH + Qpt) :
    rx - x4 ≠ 0 := by
  classical
  have havoid := famOf_avoids_affine env eb rb sb Qpt Rpt H hH hgood
  have hc0 : (famOf env eb rb sb Qpt Rpt).toAffine.coeff
      (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((3 : Fin 5), false)))))) = 3 := by
    simp only [famOf_coeff_apply]
    rfl
  have hc1 : (famOf env eb rb sb Qpt Rpt).toAffine.coeff
      (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((3 : Fin 5), true)))))) = 3 := by
    simp only [famOf_coeff_apply]
    rfl
  have hA := nsmul_ne_of_slot havoid _ hc0 (T := Rpt + -Qpt)
    (famOf_target_sh3f env eb rb sb Qpt Rpt)
  have hB := nsmul_ne_of_slot havoid _ hc1 (T := -Rpt + -Qpt)
    (famOf_target_sh3t env eb rb sb Qpt Rpt)
  have h2 : (3 - 0) • goodOffsetAffinePt H hH ≠ Rpt - Qpt := by
    intro heq
    refine hA ?_
    calc (3 : Nat) • goodOffsetAffinePt H hH
        = (3 - 0 : Nat) • goodOffsetAffinePt H hH := rfl
      _ = Rpt - Qpt := heq
      _ = Rpt + -Qpt := by abel
  have h3 : (0 + 3) • goodOffsetAffinePt H hH ≠ -(Rpt + Qpt) := by
    intro heq
    refine hB ?_
    calc (3 : Nat) • goodOffsetAffinePt H hH
        = (0 + 3 : Nat) • goodOffsetAffinePt H hH := rfl
      _ = -(Rpt + Qpt) := heq
      _ = -Rpt + -Qpt := by abel
  have hne := X_ne_of_avoids_sharp hr h4ns (goodOffsetAffinePt H hH) 0 3 Rpt Qpt
    (by rw [hRpt]; simp)
    h4pt
    (by omega) (fun _ => h2) h3
  exact sub_ne_zero.mpr hne

/-- `hs5`: `x(R) ≠ x(-3H + Q)`. -/
theorem hs5_dx (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) (H : AffinePoint K) (hH : H.IsOnCurve params)
    (hgood : GoodOffset H hH (famOf env eb rb sb Qpt Rpt))
    (rx ry : Fp) (hr : NS rx ry) (hRpt : Rpt = Affine.Point.some rx ry hr)
    (x5 y5 : Fp) (h5ns : NS x5 y5)
    (h5pt : Affine.Point.some x5 y5 h5ns = -(3 • goodOffsetAffinePt H hH) + Qpt) :
    rx - x5 ≠ 0 := by
  classical
  have havoid := famOf_avoids_affine env eb rb sb Qpt Rpt H hH hgood
  have hc0 : (famOf env eb rb sb Qpt Rpt).toAffine.coeff
      (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((4 : Fin 5), false)))))) = 3 := by
    simp only [famOf_coeff_apply]
    rfl
  have hc1 : (famOf env eb rb sb Qpt Rpt).toAffine.coeff
      (slotEquiv (Sum.inr (Sum.inr (Sum.inr (Sum.inl ((4 : Fin 5), true)))))) = 3 := by
    simp only [famOf_coeff_apply]
    rfl
  have hA := nsmul_ne_of_slot havoid _ hc0 (T := Qpt + -Rpt)
    (famOf_target_sh4f env eb rb sb Qpt Rpt)
  have hB := nsmul_ne_of_slot havoid _ hc1 (T := Qpt + Rpt)
    (famOf_target_sh4t env eb rb sb Qpt Rpt)
  -- the wire holds `-3H + Q = -(3H - Q)`; negation preserves `x`
  have h5pt' : Affine.Point.some x5 (-y5) (negPt_ns h5ns)
      = 3 • goodOffsetAffinePt H hH + (-Qpt) := by
    rw [negPt_group x5 y5 h5ns, h5pt]
    abel
  have h2 : (3 - 0) • goodOffsetAffinePt H hH ≠ Rpt - (-Qpt) := by
    intro heq
    refine hB ?_
    calc (3 : Nat) • goodOffsetAffinePt H hH
        = (3 - 0 : Nat) • goodOffsetAffinePt H hH := rfl
      _ = Rpt - (-Qpt) := heq
      _ = Qpt + Rpt := by abel
  have h3 : (0 + 3) • goodOffsetAffinePt H hH ≠ -(Rpt + (-Qpt)) := by
    intro heq
    refine hA ?_
    calc (3 : Nat) • goodOffsetAffinePt H hH
        = (0 + 3 : Nat) • goodOffsetAffinePt H hH := rfl
      _ = -(Rpt + (-Qpt)) := heq
      _ = Qpt + -Rpt := by abel
  have hne := X_ne_of_avoids_sharp hr (negPt_ns h5ns) (goodOffsetAffinePt H hH) 0 3 Rpt (-Qpt)
    (by rw [hRpt]; simp)
    h5pt'
    (by omega) (fun _ => h2) h3
  exact sub_ne_zero.mpr hne

/-! ## The `ℤ`-coefficient bridge

The ladder accumulator's `H`-coefficient is `(-1)^(j+1)` and its table entry's is
`3·(-1)^j`, so the ladder denominators need the bridge with **integer**
coefficients.  The two lemmas below are the `ℤ` analogues of
`X_eq_imp_bad` / `X_ne_of_avoids_sharp`; the proofs are the same, with
`sub_zsmul` / `add_zsmul` in place of `nsmul_sub_of_add_eq` / `add_nsmul`.
-/

/-- `[a]H + B₀ = [b]H + B₁` with `b ≤ a` gives `[a-b]H = B₁ - B₀`. -/
theorem zsmul_sub_of_add_eq {Hpt B0 B1 : Affine.Point Wp} {a b : ℤ}
    (h : a • Hpt + B0 = b • Hpt + B1) (hba : b ≤ a) :
    (a - b) • Hpt = B1 - B0 := by
  have h1 : a • Hpt - b • Hpt = B1 - B0 := by
    have h2 : a • Hpt - b • Hpt + B0 = B1 := by
      rw [show a • Hpt - b • Hpt + B0 = a • Hpt + B0 - b • Hpt from by abel, h]
      abel
    exact eq_sub_of_add_eq h2
  have h3 : (a - b) • Hpt = a • Hpt - b • Hpt := sub_zsmul Hpt a b
  rw [h3]
  exact h1

/-- **Same `x` implies one of the three bad equations**, `ℤ`-coefficient form. -/
theorem X_eq_imp_bad_zsmul {xP yP xQ yQ : Fp} (hP : NS xP yP) (hQ : NS xQ yQ)
    (Hpt : Affine.Point Wp) (a b : ℤ) (B0 B1 : Affine.Point Wp)
    (hPpt : Affine.Point.some xP yP hP = a • Hpt + B0)
    (hQpt : Affine.Point.some xQ yQ hQ = b • Hpt + B1)
    (hx : xP = xQ) :
    (b ≤ a ∧ (a - b) • Hpt = B1 - B0) ∨
      (a ≤ b ∧ (b - a) • Hpt = B0 - B1) ∨
      (a + b) • Hpt = -(B0 + B1) := by
  subst hx
  rcases some_eq_or_neg_of_X_eq hP hQ with h | h
  · have heq : a • Hpt + B0 = b • Hpt + B1 := by rw [← hPpt, h, hQpt]
    rcases le_total b a with hba | hab
    · exact Or.inl ⟨hba, zsmul_sub_of_add_eq heq hba⟩
    · exact Or.inr (Or.inl ⟨hab, zsmul_sub_of_add_eq heq.symm hab⟩)
  · right; right
    have heq : a • Hpt + B0 = -(b • Hpt + B1) := by rw [← hPpt, h, hQpt]
    have h1 : a • Hpt + B0 + (b • Hpt + B1) = 0 := by rw [heq]; abel
    have h3 : (a + b) • Hpt + (B0 + B1) = 0 := by
      rw [add_zsmul, ← h1]; abel
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using h3)

/-- **The bridge, `ℤ`-coefficient form.** -/
theorem X_ne_of_avoids_zsmul {xP yP xQ yQ : Fp} (hP : NS xP yP) (hQ : NS xQ yQ)
    (Hpt : Affine.Point Wp) (a b : ℤ) (B0 B1 : Affine.Point Wp)
    (hPpt : Affine.Point.some xP yP hP = a • Hpt + B0)
    (hQpt : Affine.Point.some xQ yQ hQ = b • Hpt + B1)
    (h1 : b ≤ a → (a - b) • Hpt ≠ B1 - B0)
    (h2 : a ≤ b → (b - a) • Hpt ≠ B0 - B1)
    (h3 : (a + b) • Hpt ≠ -(B0 + B1)) :
    xP ≠ xQ := by
  intro hx
  rcases X_eq_imp_bad_zsmul hP hQ Hpt a b B0 B1 hPpt hQpt hx with ⟨h, he⟩ | ⟨h, he⟩ | he
  · exact h1 h he
  · exact h2 h he
  · exact h3 he

end StandardECDSA.Phases
