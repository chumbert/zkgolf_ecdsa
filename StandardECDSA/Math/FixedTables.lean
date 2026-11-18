/-
# Fixed generator tables and the fixed-base shift

Ported from the pinned `circuit_baseline` revision
(`3a1bd20749ae0b6400a158651dba64a2c5fc58ff`), `Baseline/Projected/Offset.lean`
(`KP`, `affine`, `gPoint`, `mulG`, `fixedTables`, `fixedShift`).

The fixed-base phase consumes, for each window `i < 128` and digit `d ∈ {0,1,2,3}`,
the affine point `[(4 + d)·4^i]G`, and starts from the shift
`S = [4·(4^128 - 1)/3]G` so that the prefix invariant of plan §5 holds.

Task T11 certifies each of the `128·4` entries and the shift in the kernel; this
module only *defines* them, so that the circuit of task T05/T12 can run.
-/

import StandardECDSA.Gadgets.Field
import StandardECDSA.Math.GroupOrder
import ECDSA.EC

namespace StandardECDSA.Math.FixedTables

open StandardECDSA
open StandardECDSA.Gadgets
open WeierstrassCurve
open scoped BigOperators

abbrev KP := ProjectivePoint Fp

/-- Affine coordinates of a finite projective point. -/
def affine (p : KP) : Fp × Fp := (p.X * p.Z⁻¹, p.Y * p.Z⁻¹)

/-- The P-256 generator in projective coordinates. -/
def gPoint : KP := { X := gx, Y := gy, Z := 1 }

/-- `[k]G` for a natural number `k`, reduced modulo the group order. -/
def mulG (k : Nat) : KP :=
  bsmul (padBits (natToBits (k % Challenge.Specs.ECDSAP256.n)) 256)
    gPoint Challenge.Specs.ECDSAP256.params

/-- Constants only: `[(4+d)·4^i]G` for `d = 0..3`; none is infinity. -/
def fixedTables : Array (Array (Fp × Fp)) :=
  (List.range 128).toArray.map fun i =>
    (List.range 4).toArray.map fun d => affine (mulG ((4 + d) * 4 ^ i))

/-- The fixed-base shift `S = [4·(4^128 - 1)/3]G`. -/
def fixedShift : Fp × Fp := affine (mulG (4 * ((4 ^ 128 - 1) / 3)))


/-! ## Certification of `mulG` (task T11)

`mulG k` is the vendored projective `bsmul` of the generator by `k % n`.  The
certification below is done at the *group* level: `mulG k` is proved to be the
Mathlib point `k • Gpt`, which is enough to identify its affine coordinates with
those of `k • G` without ever kernel-evaluating a 256-step `bsmul`. -/

/-- `mulG k` is on the curve. -/
abbrev mulG_on_curve (k : Nat) : (mulG k).IsOnCurve params :=
  bsmul_on_curve (padBits (natToBits (k % n)) 256) gPoint params gPoint_on_curve

/-- `mulG k` is the Mathlib group element `k • G`. -/
theorem mulG_toMathlib (k : Nat) :
    (mulG k).toMathlibPoint params (mulG_on_curve k) = k • Gpt := by
  have h := toMathlibPoint_bsmul (padBits (natToBits (k % n)) 256) gPoint params gPoint_on_curve
  rw [bitsToNat_padBits] at h
  have h2 : k • Gpt = (k % n) • Gpt := by
    conv_lhs => rw [show k = n * (k / n) + k % n from (Nat.div_add_mod k n).symm]
    rw [add_nsmul, mul_nsmul, nsmul_n_Gpt, nsmul_zero, zero_add]
  rw [h2]
  exact h

/-- `mulG k` is finite (`Z ≠ 0`) for `0 < k < n`. -/
theorem mulG_Z_ne_zero {k : Nat} (hk0 : 0 < k) (hkn : k < n) : (mulG k).Z ≠ 0 := by
  intro hz
  have hX : (mulG k).X = 0 :=
    ProjectivePoint.X_eq_zero_of_Z_eq_zero (mulG k) params (mulG_on_curve k) hz
  have hY : (mulG k).Y ≠ 0 :=
    ProjectivePoint.Y_ne_zero_of_Z_eq_zero (mulG k) params (mulG_on_curve k) hz
  have heq : ProjectiveEquiv (mulG k) infinityPoint := by
    refine ⟨(mulG k).Y, hY, ?_⟩
    ext <;> simp [infinityPoint, hX, hz]
  have h0 : (mulG k).toMathlibPoint params (mulG_on_curve k) = 0 := by
    rw [← toMathlibPoint_infinity params (infinity_on_curve params)]
    exact (toMathlibPoint_eq_iff_ProjectiveEquiv _ _ params _ _).mpr heq
  rw [mulG_toMathlib] at h0
  have hdvd : addOrderOf Gpt ∣ k := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
  rw [addOrderOf_Gpt] at hdvd
  have := Nat.le_of_dvd hk0 hdvd
  omega

/-! ## Affine coordinates -/

/-- The affine point of the Mathlib group attached to a finite projective point. -/
noncomputable def toAffinePt (p : KP) (hP : p.IsOnCurve params) (hz : p.Z ≠ 0) :
    Affine.Point (params.toMathlib.toAffine) :=
  WeierstrassCurve.Projective.Point.toAffine params.toMathlib p.toMathlib

/-- The affine generator. -/
noncomputable def GptAff : Affine.Point (params.toMathlib.toAffine) :=
  WeierstrassCurve.Projective.Point.toAffineLift Gpt

/-- Nonsingularity of the affine coordinates of a finite on-curve point. -/
theorem affine_ns (p : KP) (hP : p.IsOnCurve params) (hz : p.Z ≠ 0) :
    Affine.Nonsingular (params.toMathlib.toAffine) (affine p).1 (affine p).2 := by
  have hP' : WeierstrassCurve.Projective.Nonsingular params.toMathlib p.toMathlib :=
    isOnCurve_implies_nonsingular p params hP
  have hz' : p.toMathlib 2 ≠ 0 := hz
  exact (WeierstrassCurve.Projective.nonsingular_of_Z_ne_zero hz').mp hP'

/-- `toAffinePt` is `toAffineLift` of the Mathlib point. -/
theorem toAffinePt_eq_toAffineLift (p : KP) (hP : p.IsOnCurve params) (hz : p.Z ≠ 0) :
    toAffinePt p hP hz
      = WeierstrassCurve.Projective.Point.toAffineLift (p.toMathlibPoint params hP) := rfl

/-- `toAffinePt` has the coordinates `affine p`. -/
theorem toAffinePt_eq_some (p : KP) (hP : p.IsOnCurve params) (hz : p.Z ≠ 0) :
    toAffinePt p hP hz
      = Affine.Point.some (affine p).1 (affine p).2 (affine_ns p hP hz) := by
  rw [toAffinePt]
  have hP' : WeierstrassCurve.Projective.Nonsingular params.toMathlib p.toMathlib :=
    isOnCurve_implies_nonsingular p params hP
  rw [WeierstrassCurve.Projective.Point.toAffine_of_Z_ne_zero (W := params.toMathlib) hP'
    (show p.toMathlib 2 ≠ 0 from hz)]
  simp only [Affine.Point.some.injEq]
  refine ⟨?_, ?_⟩ <;> simp [affine, ProjectivePoint.toMathlib, div_eq_mul_inv]

/-- **`mulG` affine semantics.**  For `0 < k < n`, the affine coordinates of
`mulG k` denote the group element `k • G`. -/
theorem mulG_affine_eq (k : Nat) (hk0 : 0 < k) (hkn : k < n) :
    toAffinePt (mulG k) (mulG_on_curve k) (mulG_Z_ne_zero hk0 hkn) = k • GptAff := by
  rw [toAffinePt_eq_toAffineLift, mulG_toMathlib]
  exact map_nsmul (WeierstrassCurve.Projective.Point.toAffineAddEquiv (params.toMathlib)) k Gpt

/-- The `Affine.Point.some` form of `mulG_affine_eq`. -/
theorem mulG_affine_some (k : Nat) (hk0 : 0 < k) (hkn : k < n) :
    Affine.Point.some (affine (mulG k)).1 (affine (mulG k)).2
        (affine_ns (mulG k) (mulG_on_curve k) (mulG_Z_ne_zero hk0 hkn))
      = k • GptAff := by
  rw [← toAffinePt_eq_some]
  exact mulG_affine_eq k hk0 hkn

/-! ## The fixed tables -/

/-- The table entry `[(4+d)·4^i]G` as a pair of field elements. -/
def tableEntry (i d : Nat) : Fp × Fp := affine (mulG ((4 + d) * 4 ^ i))

/-- The fixed-base shift `S = [4·Σ_{i<128}4^i]G` as a natural number. -/
def shiftNat : Nat := 4 * ((4 ^ 128 - 1) / 3)

theorem fixedTables_size : fixedTables.size = 128 := by
  simp only [fixedTables, Array.size_map, List.size_toArray, List.length_range]

theorem fixedTables_row_size (i : Nat) (hi : i < fixedTables.size) :
    (fixedTables[i]'hi).size = 4 := by
  have h1 : fixedTables[i]'hi
      = (List.range 4).toArray.map (fun d => affine (mulG ((4 + d) * 4 ^ i))) := by
    simp only [fixedTables, Array.getElem_map, List.getElem_toArray, List.getElem_range]
  rw [h1, Array.size_map, List.size_toArray, List.length_range]

theorem fixedTables_get (i d : Nat) (hi : i < fixedTables.size)
    (hs : d < (fixedTables[i]'hi).size) :
    (fixedTables[i]'hi)[d]'hs = tableEntry i d := by
  simp only [fixedTables, tableEntry, Array.getElem_map, List.getElem_toArray,
    List.getElem_range]

theorem fixedShift_eq : fixedShift = affine (mulG shiftNat) := rfl

/-! ## Window sum and cancellation -/

theorem geom_sum_four : (∑ i ∈ Finset.range 128, 4 ^ i) * 3 = 4 ^ 128 - 1 := by
  have h : ∀ m : Nat, (∑ i ∈ Finset.range m, 4 ^ i) * 3 = 4 ^ m - 1 := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, add_mul, ih, Nat.pow_succ]
      have h4 : 0 < 4 ^ k := pow_pos (by decide : (0:Nat) < 4) k
      omega
  exact h 128

theorem shiftNat_eq : shiftNat = 4 * ∑ i ∈ Finset.range 128, 4 ^ i := by
  unfold shiftNat
  rw [← geom_sum_four, Nat.mul_comm (∑ i ∈ Finset.range 128, 4 ^ i) 3,
    Nat.mul_div_right _ (by norm_num : 0 < 3)]

/-- **Window sum.**  The 128 window constants sum to the shift plus the digest. -/
theorem window_sum (d : Nat → Nat) :
    (∑ i ∈ Finset.range 128, (4 + d i) * 4 ^ i)
      = shiftNat + ∑ i ∈ Finset.range 128, d i * 4 ^ i := by
  have h : ∀ i, (4 + d i) * 4 ^ i = 4 * 4 ^ i + d i * 4 ^ i := fun i => by ring
  simp only [h, Finset.sum_add_distrib]
  rw [shiftNat_eq, Finset.mul_sum]

/-- Dependent `nsmul`-sum: `∑ f i • a = (∑ f i) • a`. -/
theorem sum_nsmul_dep {ι : Type} (s : Finset ι) (f : ι → Nat)
    {A : Type} [AddCommMonoid A] (a : A) :
    (∑ i ∈ s, f i • a) = (∑ i ∈ s, f i) • a := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, add_nsmul, ih]

/-- **Window sum in the group.**  The 128 window points sum to `S + [E]G`. -/
theorem window_sum_group (d : Nat → Nat) :
    (∑ i ∈ Finset.range 128, ((4 + d i) * 4 ^ i) • Gpt)
      = shiftNat • Gpt + (∑ i ∈ Finset.range 128, d i * 4 ^ i) • Gpt := by
  rw [sum_nsmul_dep, window_sum d, add_nsmul]

end StandardECDSA.Math.FixedTables
