/-
# Honest-witness denominators (task G1-c, fixed-base part)

`CompleteWitness` (`StandardECDSA/Main.lean`) carries the concrete distinct-`x`
denominators as explicit hypotheses.  This module discharges the fixed-base ones
from `GoodOffset`, using the affine→projective bridge of
`StandardECDSA/Math/DenominatorBridge.lean` and the explicit slot index
`StandardECDSA.Math.slotEquiv`.

The pattern, once per denominator:

* the honest-witness invariant (`fbInv`) supplies the group image
  `A_k = [1]H + B₁` of the accumulator;
* the gadget's table lemma (`muxConst4W_tablePt`) supplies the group image
  `T_k = [0]H + B₀` of the mux output;
* `X_ne_of_avoids_sharp` turns the two slots of the concrete family
  (`famOf`, `Math/OffsetFamily.lean`) into `x(T_k) ≠ x(A_k)`.
-/

import StandardECDSA.Phases.FixedBaseSemantics
import StandardECDSA.Math.OffsetFamily
import StandardECDSA.Math.DenominatorBridge

namespace StandardECDSA.Phases

open WeierstrassCurve StandardECDSA StandardECDSA.Gadgets StandardECDSA.Math
open StandardECDSA.Math.FixedTables

/-- The affine-level `Avoids` fact for the concrete family. -/
theorem famOf_avoids_affine (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) (H : AffinePoint K) (hH : H.IsOnCurve params)
    (hgood : GoodOffset H hH (famOf env eb rb sb Qpt Rpt)) :
    (famOf env eb rb sb Qpt Rpt).toAffine.Avoids (goodOffsetAffinePt H hH) :=
  goodOffset_avoids_affine H hH hgood

/-- The `fbMux` of window `k` is the constant mux over the certified table row. -/
theorem fbMux_eq (eb : Vector E 256) (k : Nat) (hk : k < 128) :
    fbMux eb fixedTables ⟨k, hk⟩
      = muxConst4W (eb.get ⟨2 * k, by omega⟩) (eb.get ⟨2 * k + 1, by omega⟩)
          (fbTab k hk) := by
  simp only [fbMux]
  rw [fixedTables_getD_row k hk]

/-- The affine target of the `fbWin` slot `(k, false)`. -/
theorem famOf_target_fbWin_false (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) (k : Nat) (hk : k < 128) :
    (famOf env eb rb sb Qpt Rpt).toAffine.target
        (slotEquiv (Sum.inr (Sum.inl ((⟨k, hk⟩ : Fin 128), false))))
      = tablePt k (digitOf env eb k) + shiftPt
        + -(WeierstrassCurve.Projective.Point.toAffineLift (winSum env eb k • Gpt)) := by
  show toAff ((famOf env eb rb sb Qpt Rpt).target
    (slotEquiv (Sum.inr (Sum.inl ((⟨k, hk⟩ : Fin 128), false))))) = _
  rw [famOf_target_apply]
  simp only [targetOf, toAff_toProjective]

/-- The affine target of the `fbWin` slot `(k, true)`. -/
theorem famOf_target_fbWin_true (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) (k : Nat) (hk : k < 128) :
    (famOf env eb rb sb Qpt Rpt).toAffine.target
        (slotEquiv (Sum.inr (Sum.inl ((⟨k, hk⟩ : Fin 128), true))))
      = -(tablePt k (digitOf env eb k)) + shiftPt
        + -(WeierstrassCurve.Projective.Point.toAffineLift (winSum env eb k • Gpt)) := by
  show toAff ((famOf env eb rb sb Qpt Rpt).target
    (slotEquiv (Sum.inr (Sum.inl ((⟨k, hk⟩ : Fin 128), true))))) = _
  rw [famOf_target_apply]
  simp only [targetOf, toAff_toProjective]

/-- **The 128 fixed-base window denominators do not vanish.**

Window `k` adds the constant table point `T_k = [(4+d_k)·4^k]G` to the
accumulator `A_k = H - S + [winSum k]G`.  A vanishing denominator would force
`[1]H = T_k + S - [winSum k]G` or `[1]H = -T_k + S - [winSum k]G`, which are
exactly the two `fbWin` slots `(k, false)` and `(k, true)` of the concrete
family. -/
theorem fbWin_dx (env : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp) (H : AffinePoint K) (hH : H.IsOnCurve params)
    (hgood : GoodOffset H hH (famOf env eb rb sb Qpt Rpt))
    (n k : Nat) (hk : k < 128) (acc : Pt)
    (hb0 : Expression.eval env (eb.get ⟨2 * k, by omega⟩) = 0
        ∨ Expression.eval env (eb.get ⟨2 * k, by omega⟩) = 1)
    (hb1 : Expression.eval env (eb.get ⟨2 * k + 1, by omega⟩) = 0
        ∨ Expression.eval env (eb.get ⟨2 * k + 1, by omega⟩) = 1)
    (hrow : Expression.eval env (pm (eb.get ⟨2 * k, by omega⟩)
        (eb.get ⟨2 * k + 1, by omega⟩) - Expression.var (F := Fp) ⟨n + k * 5⟩) = 0)
    (hacc : fbInv env eb (goodOffsetAffinePt H hH) k acc) :
    Expression.eval env ((fbMux eb fixedTables ⟨k, hk⟩).output (n + k * 5)).1
      - Expression.eval env acc.1 ≠ 0 := by
  classical
  have havoid := famOf_avoids_affine env eb rb sb Qpt Rpt H hH hgood
  have hcF : (famOf env eb rb sb Qpt Rpt).toAffine.coeff
      (slotEquiv (Sum.inr (Sum.inl ((⟨k, hk⟩ : Fin 128), false)))) = 1 := by
    simp only [famOf_coeff_apply]
    rfl
  have hcT : (famOf env eb rb sb Qpt Rpt).toAffine.coeff
      (slotEquiv (Sum.inr (Sum.inl ((⟨k, hk⟩ : Fin 128), true)))) = 1 := by
    simp only [famOf_coeff_apply]
    rfl
  have hF := nsmul_ne_of_slot havoid
    (slotEquiv (Sum.inr (Sum.inl ((⟨k, hk⟩ : Fin 128), false)))) hcF
    (T := (famOf env eb rb sb Qpt Rpt).toAffine.target
      (slotEquiv (Sum.inr (Sum.inl ((⟨k, hk⟩ : Fin 128), false))))) rfl
  have hT' := nsmul_ne_of_slot havoid
    (slotEquiv (Sum.inr (Sum.inl ((⟨k, hk⟩ : Fin 128), true)))) hcT
    (T := (famOf env eb rb sb Qpt Rpt).toAffine.target
      (slotEquiv (Sum.inr (Sum.inl ((⟨k, hk⟩ : Fin 128), true))))) rfl
  obtain ⟨hns, hval⟩ := hacc
  obtain ⟨hT0, hTval0⟩ := muxConst4W_tablePt env k hk (eb.get ⟨2 * k, by omega⟩)
    (eb.get ⟨2 * k + 1, by omega⟩) (n + k * 5) hb0 hb1 hrow
  -- the two bad equations, in the shape `X_ne_of_avoids_sharp` expects
  have h2 : (1 - 0) • goodOffsetAffinePt H hH
      ≠ tablePt k ((Expression.eval env (eb.get ⟨2 * k, by omega⟩)).val
          + 2 * (Expression.eval env (eb.get ⟨2 * k + 1, by omega⟩)).val)
        - (-shiftPt + WeierstrassCurve.Projective.Point.toAffineLift
            (winSum env eb k • Gpt)) := by
    have h := hF
    rw [famOf_target_fbWin_false env eb rb sb Qpt Rpt k hk] at h
    rw [digitOf_eq env eb k hk] at h
    intro heq
    refine h ?_
    calc (1 : Nat) • goodOffsetAffinePt H hH
        = (1 - 0 : Nat) • goodOffsetAffinePt H hH := rfl
      _ = tablePt k ((Expression.eval env (eb.get ⟨2 * k, by omega⟩)).val
            + 2 * (Expression.eval env (eb.get ⟨2 * k + 1, by omega⟩)).val)
          - (-shiftPt + WeierstrassCurve.Projective.Point.toAffineLift
              (winSum env eb k • Gpt)) := heq
      _ = tablePt k ((Expression.eval env (eb.get ⟨2 * k, by omega⟩)).val
            + 2 * (Expression.eval env (eb.get ⟨2 * k + 1, by omega⟩)).val)
          + shiftPt + -(WeierstrassCurve.Projective.Point.toAffineLift
              (winSum env eb k • Gpt)) := by abel
  have h3 : (0 + 1) • goodOffsetAffinePt H hH
      ≠ -(tablePt k ((Expression.eval env (eb.get ⟨2 * k, by omega⟩)).val
            + 2 * (Expression.eval env (eb.get ⟨2 * k + 1, by omega⟩)).val)
          + (-shiftPt + WeierstrassCurve.Projective.Point.toAffineLift
              (winSum env eb k • Gpt))) := by
    have h := hT'
    rw [famOf_target_fbWin_true env eb rb sb Qpt Rpt k hk] at h
    rw [digitOf_eq env eb k hk] at h
    intro heq
    refine h ?_
    calc (1 : Nat) • goodOffsetAffinePt H hH
        = (0 + 1 : Nat) • goodOffsetAffinePt H hH := rfl
      _ = -(tablePt k ((Expression.eval env (eb.get ⟨2 * k, by omega⟩)).val
              + 2 * (Expression.eval env (eb.get ⟨2 * k + 1, by omega⟩)).val)
            + (-shiftPt + WeierstrassCurve.Projective.Point.toAffineLift
                (winSum env eb k • Gpt))) := heq
      _ = -(tablePt k ((Expression.eval env (eb.get ⟨2 * k, by omega⟩)).val
              + 2 * (Expression.eval env (eb.get ⟨2 * k + 1, by omega⟩)).val))
          + shiftPt + -(WeierstrassCurve.Projective.Point.toAffineLift
              (winSum env eb k • Gpt)) := by abel
  have hne := X_ne_of_avoids_sharp hT0 hns (goodOffsetAffinePt H hH) 0 1
    (tablePt k ((Expression.eval env (eb.get ⟨2 * k, by omega⟩)).val
      + 2 * (Expression.eval env (eb.get ⟨2 * k + 1, by omega⟩)).val))
    (-shiftPt + WeierstrassCurve.Projective.Point.toAffineLift (winSum env eb k • Gpt))
    (by rw [hTval0]; simp)
    (by rw [hval]; simp only [one_smul]; abel)
    (by omega) (fun _ => h2) h3
  rw [fbMux_eq eb k hk]
  intro hzero
  exact hne (sub_eq_zero.mp hzero)

end StandardECDSA.Phases
