/-
# Correctness of the honest seed generator (task T16)

`Witness/Generate.lean` computes the 772-field seed.  This module proves that the
generated seed is *admissible* whenever the input is standard-valid, and that the
signature point it carries is exactly the standard verification point `V`.

The two mathematical ingredients are

* the little-endian bit decomposition `leNat (bitOf m) = m % 2^k`, which makes
  the extracted `r`, `t` and digest bits recompose to the right integers;
* the canonical overflow split `val(x(V)) = r + n·overflow`, which uses
  `n < p < 2n` and `val(x(V)) mod n = r`.

No constraint satisfaction appears in any hypothesis: admissibility is a
predicate on group points and naturals only.
-/

import StandardECDSA.Witness.Generate

namespace StandardECDSA.Witness

open StandardECDSA
open StandardECDSA.Math

set_option maxRecDepth 100000

/-! ## Bit extraction -/

/-- Every little-endian bit is `0` or `1`. -/
theorem bitOf_lt_two (m i : Nat) : bitOf m i < 2 :=
  Nat.mod_lt _ (by norm_num)

/-- The canonical value of an extracted bit. -/
theorem val_bitsOf (m : Nat) (i : Fin 256) : (bitsOf m i).val = bitOf m (i : Nat) := by
  unfold bitsOf
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
  exact lt_trans (bitOf_lt_two m _) (by decide)

/-- Splitting a little-endian sum at its last index. -/
theorem leNat_succ {k : Nat} (v : Fin (k + 1) → Nat) :
    leNat v = leNat (fun i : Fin k => v (Fin.castSucc i)) + 2 ^ k * v (Fin.last k) := by
  unfold leNat
  rw [Fin.sum_univ_castSucc]
  simp [Fin.val_castSucc, Fin.val_last]

/-- **The `2^(k+1)` remainder split.** -/
theorem mod_two_pow_succ (m k : Nat) :
    m % 2 ^ (k + 1) = 2 ^ k * bitOf m k + m % 2 ^ k := by
  have hb : bitOf m k ≤ 1 := by
    have := bitOf_lt_two m k
    omega
  have hr : m % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  have hX : 2 ^ k * bitOf m k + m % 2 ^ k < 2 ^ k * 2 := by
    nlinarith [Nat.two_pow_pos k]
  have hd : m / 2 ^ k = 2 * ((m / 2 ^ k) / 2) + bitOf m k := by
    unfold bitOf
    exact (Nat.div_add_mod _ 2).symm
  have hm : m = (2 ^ k * bitOf m k + m % 2 ^ k) + (2 ^ k * 2) * ((m / 2 ^ k) / 2) := by
    have h1 : m = 2 ^ k * (m / 2 ^ k) + m % 2 ^ k := (Nat.div_add_mod m (2 ^ k)).symm
    have h2 : 2 ^ k * (m / 2 ^ k) = 2 ^ k * (2 * ((m / 2 ^ k) / 2) + bitOf m k) := by
      conv_lhs => rw [hd]
    conv_lhs => rw [h1, h2]
    ring
  conv_lhs => rw [hm]
  rw [show 2 ^ (k + 1) = 2 ^ k * 2 from by rw [Nat.pow_succ]]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hX]

/-- **Little-endian bit decomposition.**  The `k` extracted bits of `m` recompose
to `m % 2^k`. -/
theorem leNat_bitOf : ∀ (k m : Nat),
    leNat (fun i : Fin k => bitOf m (i : Nat)) = m % 2 ^ k
  | 0, m => by
      have h : leNat (fun i : Fin 0 => bitOf m (i : Nat)) = 0 := by simp [leNat]
      rw [h]
      exact (Nat.mod_one m).symm
  | k + 1, m => by
      rw [leNat_succ (fun i : Fin (k + 1) => bitOf m (i : Nat))]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [leNat_bitOf k m, mod_two_pow_succ m k]
      omega

/-- The 256 extracted bits of `m` recompose to `m % 2^256`. -/
theorem leNat_bitsOf_val (m : Nat) :
    leNat (fun i : Fin 256 => (bitsOf m i).val) = m % 2 ^ 256 := by
  have h : (fun i : Fin 256 => (bitsOf m i).val) = (fun i : Fin 256 => bitOf m (i : Nat)) := by
    funext i
    exact val_bitsOf m i
  rw [h, leNat_bitOf 256 m]

/-- The low 128 extracted bits of `m` recompose to `m % 2^128`. -/
theorem leNat_low_half (m : Nat) :
    leNat (fun i : Fin 128 => bitOf m (i : Nat)) = m % 2 ^ 128 :=
  leNat_bitOf 128 m

/-- The high 128 extracted bits of `m` recompose to `m / 2^128`. -/
theorem leNat_high_half (m : Nat) (hm : m < 2 ^ 256) :
    leNat (fun i : Fin 128 => bitOf m (128 + (i : Nat))) = m / 2 ^ 128 := by
  have h1 : (fun i : Fin 128 => bitOf m (128 + (i : Nat)))
      = (fun i : Fin 128 => bitOf (m / 2 ^ 128) (i : Nat)) := by
    funext i
    unfold bitOf
    rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]
  rw [h1, leNat_bitOf 128 (m / 2 ^ 128), Nat.mod_eq_of_lt]
  by_contra hcon
  push_neg at hcon
  have h2 : 2 ^ 128 * (m / 2 ^ 128) ≤ m := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self m (2 ^ 128)
  have h3 : 2 ^ 128 * 2 ^ 128 ≤ 2 ^ 128 * (m / 2 ^ 128) := Nat.mul_le_mul_left _ hcon
  have hpow : 2 ^ 256 = 2 ^ 128 * 2 ^ 128 := by ring
  omega

/-! ## Booleanity -/

/-- The overflow bit is Boolean. -/
theorem overflowOf_bool (rx r : Nat) : overflowOf rx r = 0 ∨ overflowOf rx r = 1 := by
  unfold overflowOf
  split <;> simp

/-- Every extracted bit is Boolean as a field element. -/
theorem bitsOf_bool (m : Nat) (i : Fin 256) : bitsOf m i = 0 ∨ bitsOf m i = 1 := by
  have h := bitOf_lt_two m (i : Nat)
  have hc : bitOf m (i : Nat) = 0 ∨ bitOf m (i : Nat) = 1 := by omega
  unfold bitsOf
  rcases hc with h0 | h1
  · left; rw [h0]; simp
  · right; rw [h1]; simp

/-! ## Numeric bounds -/

/-- The group order is below `2^256`. -/
theorem n_lt_two_pow_256 : n < 2 ^ 256 := by decide

/-- The field characteristic is below `n + n`. -/
theorem p_lt_n_add_n : p < n + n := by decide

/-! ## The generated seed's components -/

/-- The generated overflow cell. -/
theorem generateSeed_overflow_val (pkX pkY digestLo digestHi r s : K)
    (fam : BadFamily Grp) (hm : fam.m < 1040) :
    (generateSeed pkX pkY digestLo digestHi r s fam hm).overflow
      = ((overflowOf (affineX (stdV { X := pkX, Y := pkY } r s
            (digestOf digestLo digestHi))).val r.val : Nat) : K) := rfl

/-- The generated `r` bits. -/
theorem generateSeed_rBits (pkX pkY digestLo digestHi r s : K)
    (fam : BadFamily Grp) (hm : fam.m < 1040) :
    (generateSeed pkX pkY digestLo digestHi r s fam hm).rBits = bitsOf r.val := rfl

/-- The generated `t` bits. -/
theorem generateSeed_tBits (pkX pkY digestLo digestHi r s : K)
    (fam : BadFamily Grp) (hm : fam.m < 1040) :
    (generateSeed pkX pkY digestLo digestHi r s fam hm).tBits = bitsOf (n - s.val) := rfl

/-- The generated digest bits. -/
theorem generateSeed_digestBits (pkX pkY digestLo digestHi r s : K)
    (fam : BadFamily Grp) (hm : fam.m < 1040) :
    (generateSeed pkX pkY digestLo digestHi r s fam hm).digestBits
      = bitsOf (digestOf digestLo digestHi) := rfl

/-- The generated seed's scalar facts. -/
theorem generateSeed_scalarFacts (pkX pkY digestLo digestHi r s : K)
    (fam : BadFamily Grp) (hm : fam.m < 1040)
    (hrn : r.val < n) (hs0 : 0 < s.val)
    (hlo : digestLo.val < 2 ^ 128) (hhi : digestHi.val < 2 ^ 128) :
    ScalarFacts (generateSeed pkX pkY digestLo digestHi r s fam hm)
      (digestOf digestLo digestHi) r.val (n - s.val) := by
  have hE : digestOf digestLo digestHi < 2 ^ 256 :=
    digest_toNat_lt digestLo digestHi hlo hhi
  have hn := n_lt_two_pow_256
  have ht : n - s.val < 2 ^ 256 := by omega
  have hov := generateSeed_overflow_val pkX pkY digestLo digestHi r s fam hm
  have hrb := generateSeed_rBits pkX pkY digestLo digestHi r s fam hm
  have htb := generateSeed_tBits pkX pkY digestLo digestHi r s fam hm
  have hdb := generateSeed_digestBits pkX pkY digestLo digestHi r s fam hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hov]
    rcases overflowOf_bool _ _ with h | h <;> rw [h] <;> simp
  · simp only [hrb]
    intro i; exact bitsOf_bool _ i
  · simp only [htb]
    intro i; exact bitsOf_bool _ i
  · simp only [hdb]
    intro i; exact bitsOf_bool _ i
  · simp only [hrb, leNat_bitsOf_val, Nat.mod_eq_of_lt]
    omega
  · simp only [htb, leNat_bitsOf_val, Nat.mod_eq_of_lt]
    omega
  · simp only [hdb]
    have h : (fun i : Fin 128 => (bitsOf (digestOf digestLo digestHi)
          (Fin.castLE (by norm_num) i)).val)
        = (fun i : Fin 128 => bitOf (digestOf digestLo digestHi) (i : Nat)) := by
      funext i
      rw [val_bitsOf]
      rfl
    rw [h, leNat_low_half]
  · simp only [hdb]
    have h : (fun i : Fin 128 => (bitsOf (digestOf digestLo digestHi)
          (Fin.natAdd 128 i)).val)
        = (fun i : Fin 128 => bitOf (digestOf digestLo digestHi) (128 + (i : Nat))) := by
      funext i
      rw [val_bitsOf]
      rfl
    rw [h, leNat_high_half _ hE]

/-- The generated seed's offset is on the curve. -/
theorem generateSeed_H_onCurve (pkX pkY digestLo digestHi r s : K)
    (fam : BadFamily Grp) (hm : fam.m < 1040) :
    (Seed.H (generateSeed pkX pkY digestLo digestHi r s fam hm)).IsOnCurve params :=
  affinePt_isOnCurve (generateSeed_offsetPt_on_curve pkX pkY digestLo digestHi r s fam hm)
    (generateSeed_offsetPt_Z_ne_zero pkX pkY digestLo digestHi r s fam hm)

/-- The generated seed's offset avoids every bad equation. -/
theorem generateSeed_goodOffset (pkX pkY digestLo digestHi r s : K)
    (fam : BadFamily Grp) (hm : fam.m < 1040)
    (hH : (Seed.H (generateSeed pkX pkY digestLo digestHi r s fam hm)).IsOnCurve params) :
    GoodOffset (Seed.H (generateSeed pkX pkY digestLo digestHi r s fam hm)) hH fam := by
  have hZ := generateSeed_offsetPt_Z_ne_zero pkX pkY digestLo digestHi r s fam hm
  have hP_on := generateSeed_offsetPt_on_curve pkX pkY digestLo digestHi r s fam hm
  have hpe : ProjectiveEquiv (offsetPt (findGoodOffset fam hm).val)
      ((Seed.H (generateSeed pkX pkY digestLo digestHi r s fam hm)).toProjective) :=
    projectiveEquiv_affinePt hZ
  have hpt : (offsetPt (findGoodOffset fam hm).val).toMathlibPoint params hP_on
      = ((Seed.H (generateSeed pkX pkY digestLo digestHi r s fam hm)).toProjective).toMathlibPoint
          params (affine_to_projective_on_curve _ params hH) :=
    (projectiveEquiv_iff_toMathlib _ _ hP_on _).mp hpe
  refine ⟨?_, ?_⟩
  · show (1 : K) ≠ 0
    exact one_ne_zero
  · intro i
    rw [← hpt, generateSeed_offsetPt_toMathlib pkX pkY digestLo digestHi r s fam hm]
    exact findGoodOffset_spec fam hm i

/-- **The generated seed is admissible.** -/
theorem generateSeed_complete (pkX pkY digestLo digestHi r s : K)
    (fam : BadFamily Grp) (hm : fam.m < 1040)
    (hstd : standardVerify pkX pkY digestLo digestHi r s)
    (hlo : digestLo.val < 2 ^ 128) (hhi : digestHi.val < 2 ^ 128) :
    Admissible (generateSeed pkX pkY digestLo digestHi r s fam hm)
      (affineX (stdV { X := pkX, Y := pkY } r s (digestOf digestLo digestHi)))
      (digestOf digestLo digestHi) r.val (n - s.val)
      (generateSeed_H_onCurve pkX pkY digestLo digestHi r s fam hm) fam := by
  obtain ⟨_hQ, _hr0, hrn, hs0, _hsn, _⟩ := hstd
  exact ⟨generateSeed_scalarFacts pkX pkY digestLo digestHi r s fam hm hrn hs0 hlo hhi,
    generateSeed_goodOffset pkX pkY digestLo digestHi r s fam hm _⟩

/-! ## The signature point carried by the seed -/

/-- The seed's signature point is the affine point of the standard verification
point `V`. -/
theorem generateSeed_R_eq (pkX pkY digestLo digestHi r s : K)
    (fam : BadFamily Grp) (hm : fam.m < 1040) :
    Seed.R (generateSeed pkX pkY digestLo digestHi r s fam hm)
        (affineX (stdV { X := pkX, Y := pkY } r s (digestOf digestLo digestHi)))
      = affinePt (stdV { X := pkX, Y := pkY } r s (digestOf digestLo digestHi)) := rfl

/-- The seed's signature point is on the curve for standard-valid input. -/
theorem generateSeed_R_onCurve (pkX pkY digestLo digestHi r s : K)
    (fam : BadFamily Grp) (hm : fam.m < 1040)
    (hstd : standardVerify pkX pkY digestLo digestHi r s) :
    (Seed.R (generateSeed pkX pkY digestLo digestHi r s fam hm)
        (affineX (stdV { X := pkX, Y := pkY } r s (digestOf digestLo digestHi)))).IsOnCurve
      params := by
  have hV_on : (stdV { X := pkX, Y := pkY } r s (digestOf digestLo digestHi)).IsOnCurve params :=
    stdV_on_curve _ hstd.1 r s _
  have hVne : ¬ ProjectiveEquiv
      (stdV { X := pkX, Y := pkY } r s (digestOf digestLo digestHi)) infinityPoint :=
    hstd.2.2.2.2.2.1
  have hVz : (stdV { X := pkX, Y := pkY } r s (digestOf digestLo digestHi)).Z ≠ 0 :=
    fun hz => hVne ((Z_eq_zero_iff_equiv_infinity hV_on).mp hz)
  exact affinePt_isOnCurve hV_on hVz

/-- The seed's signature point reduces to `r` modulo the group order. -/
theorem generateSeed_R_x (pkX pkY digestLo digestHi r s : K)
    (fam : BadFamily Grp) (hm : fam.m < 1040)
    (hstd : standardVerify pkX pkY digestLo digestHi r s) :
    (Seed.R (generateSeed pkX pkY digestLo digestHi r s fam hm)
        (affineX (stdV { X := pkX, Y := pkY } r s (digestOf digestLo digestHi)))).X.val % n
      = r.val :=
  hstd.2.2.2.2.2.2

/-- The affine `x`-coordinate of the standard verification point. -/
noncomputable def stdVx (pkX pkY digestLo digestHi r s : K) : K :=
  affineX (stdV { X := pkX, Y := pkY } r s (digestOf digestLo digestHi))

/-- **The canonical overflow split** (pure arithmetic).  For `r < n`, `x < p` and
`p < n + n`, the residue `x mod n = r` forces `x = r + n·overflow` with the
canonical Boolean `overflow`. -/
theorem overflow_split {x r : Nat} (hrn : r < n) (hxlt : x < p) (hp2 : p < n + n)
    (hxmod : x % n = r) :
    x = r + n * overflowOf x r := by
  unfold overflowOf
  split
  · rename_i hlt
    rw [Nat.mul_zero, Nat.add_zero]
    rw [Nat.mod_eq_of_lt hlt] at hxmod
    exact hxmod
  · rename_i hge
    push_neg at hge
    rw [Nat.mul_one]
    have hdm : n * (x / n) + x % n = x := Nat.div_add_mod x n
    have hlt : x < n + n := by omega
    have hq : x / n = 1 := by
      have h2 : x / n < 2 := by
        by_contra hc
        push_neg at hc
        have h4 : 2 * n ≤ x / n * n := Nat.mul_le_mul_right n hc
        have h6 : x / n * n ≤ n * (x / n) + x % n := by
          rw [Nat.mul_comm (x / n) n]
          exact Nat.le_add_right _ _
        have h5 : x / n * n ≤ x := by
          rw [hdm] at h6
          exact h6
        omega
      have h0 : 0 < x / n := by
        by_contra hc
        push_neg at hc
        have hz : x / n = 0 := Nat.le_zero.mp hc
        rw [hz, Nat.mul_zero, Nat.zero_add] at hdm
        omega
      omega
    rw [hq, Nat.mul_one] at hdm
    omega

/-- **The canonical overflow split.**  For standard-valid input the affine
`x`-coordinate of `V` is exactly `r + n·overflow`, so the circuit's
`rx = r + n·overflow` branch is consistent. -/
theorem generateSeed_overflow (pkX pkY digestLo digestHi r s : K)
    (hstd : standardVerify pkX pkY digestLo digestHi r s) :
    (stdVx pkX pkY digestLo digestHi r s).val
      = r.val + n * overflowOf (stdVx pkX pkY digestLo digestHi r s).val r.val :=
  overflow_split hstd.2.2.1 (ZMod.val_lt _) p_lt_n_add_n hstd.2.2.2.2.2.2

end StandardECDSA.Witness
