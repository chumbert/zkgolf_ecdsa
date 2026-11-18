/-
# Scalar encoding: bits, naturals, and canonical field values

This module supplies the pure mathematical facts used by the scalar phase of the
standard circuit:

* `bitsToNat`/`natToBits` round trips (MSB-first, matching the vendored
  `ECDSA.bsmul` bit list);
* little-endian bit-sum reconstruction, which is the form the circuit's digest
  and scalar bindings use, together with the bound `leNat v < 2^k` that keeps the
  sum below the field characteristic;
* canonical natural values of field elements, and the digest-limb bound.

Everything is proved in the kernel; no `native_decide` is used.
-/

import StandardECDSA.Spec
import ECDSA.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic

namespace StandardECDSA.Math

open StandardECDSA
open scoped BigOperators

set_option maxRecDepth 100000

/-! ## MSB-first bit lists -/

/-- Reversing an MSB-first bit list and evaluating it LSB-first gives the same value. -/
theorem bitsToNat_reverse (l : List Bool) : bitsToNat l.reverse = bitsToNatLSB l := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
      rw [List.reverse_cons]
      have h1 : bitsToNat (bs.reverse ++ [b])
          = bitsToNat bs.reverse * 2 + (if b then 1 else 0) := by
        unfold bitsToNat
        rw [List.foldl_append]
        rw [foldl_bitsToNat_general [b] (List.foldl (fun acc b => acc * 2 + (if b then 1 else 0)) 0 bs.reverse)]
        simp
      rw [h1, ih]
      simp only [bitsToNatLSB]
      omega

/-- `bitsToNat` inverts `natToBits`. -/
theorem bitsToNat_natToBits (n : Nat) : bitsToNat (natToBits n) = n := by
  unfold natToBits
  rw [bitsToNat_reverse, bitsToNatLSB_bits]

/-- Padding with `false` on the left does not change the value. -/
theorem bitsToNat_padBits (l : List Bool) (k : Nat) : bitsToNat (padBits l k) = bitsToNat l :=
  bitsToNat_padBits_eq_bitsToNat l k

/-- The MSB-first bit list of `n` has length at most `k` when `n < 2^k`. -/
theorem natToBits_length_le (n k : Nat) (h : n < 2 ^ k) : (natToBits n).length ≤ k :=
  natToBits_length n k h

/-! ## Little-endian bit sums

The circuit binds a limb to 128 Boolean bits by the *little-endian* sum
`∑ i, 2^i * bit i`.  We develop the natural-number version and transport it to
the field.
-/

/-- Little-endian reconstruction of a natural from `k` bits. -/
def leNat {k : Nat} (v : Fin k → Nat) : Nat := ∑ i : Fin k, 2 ^ (i : Nat) * v i

/-- Little-endian reconstruction in the field. -/
def leSum {k : Nat} (v : Fin k → K) : K := ∑ i : Fin k, (2 : K) ^ (i : Nat) * v i

/-- A little-endian sum of `k` bits is below `2^k`. -/
theorem leNat_lt : ∀ {k : Nat} (v : Fin k → Nat), (∀ i, v i ≤ 1) → leNat v < 2 ^ k
  | 0, v, _ => by
      have : leNat v = 0 := by simp [leNat]
      rw [this]
      exact Nat.two_pow_pos 0
  | k + 1, v, hv => by
      have hsplit : leNat v
          = leNat (fun i : Fin k => v (Fin.castSucc i)) + 2 ^ k * v (Fin.last k) := by
        unfold leNat
        rw [Fin.sum_univ_castSucc]
        rfl
      rw [hsplit]
      have ih := leNat_lt (fun i : Fin k => v (Fin.castSucc i)) (fun i => hv _)
      have hlast : v (Fin.last k) ≤ 1 := hv _
      have : 2 ^ k * v (Fin.last k) ≤ 2 ^ k := by
        calc 2 ^ k * v (Fin.last k) ≤ 2 ^ k * 1 := Nat.mul_le_mul_left _ hlast
          _ = 2 ^ k := Nat.mul_one _
      have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      omega

/-- Casting a little-endian natural sum into the field gives the field sum. -/
theorem leSum_eq_leNat {k : Nat} (v : Fin k → Nat) :
    leSum (fun i => (v i : K)) = (leNat v : K) := by
  unfold leSum leNat
  push_cast
  rfl

/-- A field little-endian sum of Boolean values, read back as a natural, is the
natural little-endian sum.  This is the bridge used by the digest and scalar
bindings: the sum is below `2^k ≤ 2^256 < p`, so no reduction modulo `p` occurs. -/
theorem val_leSum {k : Nat} (v : Fin k → K) (hv : ∀ i, v i = 0 ∨ v i = 1)
    (hk : 2 ^ k ≤ p) :
    (leSum v).val = leNat (fun i => (v i).val) := by
  haveI : Fact (1 < p) := ⟨by decide⟩
  have hbits : ∀ i, (v i).val ≤ 1 := by
    intro i
    rcases hv i with h | h
    · rw [h, ZMod.val_zero]; norm_num
    · rw [h]
      have h1 : (1 : K).val = 1 := ZMod.val_one p
      omega
  have hlt : leNat (fun i => (v i).val) < 2 ^ k := leNat_lt _ hbits
  have h1 : leSum v = leSum (fun i => ((v i).val : K)) := by
    unfold leSum
    refine Finset.sum_congr rfl fun i _ => ?_
    show (2 : K) ^ (i : Nat) * v i = (2 : K) ^ (i : Nat) * ((v i).val : K)
    rcases hv i with h | h
    · rw [h]; simp
    · rw [h]; simp
  rw [h1, leSum_eq_leNat, ZMod.val_cast_of_lt (lt_of_lt_of_le hlt hk)]

/-! ## Canonical field values -/

/-- The canonical representative of a field element is below the characteristic. -/
theorem val_lt (x : K) : x.val < p := ZMod.val_lt x

/-- Casting a natural below `p` to the field and back is the identity. -/
theorem val_cast_of_lt {m : Nat} (h : m < p) : ((m : K).val : Nat) = m :=
  ZMod.val_cast_of_lt h

/-! ## Digest limbs -/

/-- A 128-bit limb is below `2^128`. -/
theorem limb_lt (x : K) (h : x.val < 2 ^ 128) : x.val < 2 ^ 128 := h

/-- The full digest `E = lo + 2^128 * hi` of two 128-bit limbs is below `2^256`. -/
theorem digest_toNat_lt (lo hi : K) (hlo : lo.val < 2 ^ 128) (hhi : hi.val < 2 ^ 128) :
    (Digest.mk lo hi).toNat < 2 ^ 256 := by
  show lo.val + 2 ^ 128 * hi.val < 2 ^ 256
  have h2 : 2 ^ 128 * hi.val < 2 ^ 128 * 2 ^ 128 := Nat.mul_lt_mul_of_pos_left hhi (by norm_num)
  have h3 : 2 ^ 128 * 2 ^ 128 = 2 ^ 256 := by ring
  omega

/-! ## Digest window decomposition

The fixed-base phase consumes the 256 digest bits two at a time: window `i` uses
bits `2i` and `2i+1` with digit `d_i = b_{2i} + 2·b_{2i+1}`.  The lemmas below
identify the window sum `∑ d_i·4^i` with the little-endian natural `leNat b`.
-/

/-- `leNat` as a `Finset.range` sum (avoids `Fin`-indexed sums downstream). -/
theorem leNat_eq_sum_range (b : Fin 256 → Nat) :
    leNat b
      = ∑ j ∈ Finset.range 256, 2 ^ j * b ⟨j % 256, Nat.mod_lt _ (by norm_num)⟩ := by
  rw [leNat, ← Fin.sum_univ_eq_sum_range
    (fun j => 2 ^ j * b ⟨j % 256, Nat.mod_lt _ (by norm_num)⟩) 256]
  refine Finset.sum_congr rfl ?_
  intro j _
  simp [Nat.mod_eq_of_lt j.isLt]

/-- Window digit `d_i = b_{2i} + 2·b_{2i+1}` of a 256-bit vector. -/
def windowDigit (b : Fin 256 → Nat) (i : Nat) : Nat :=
  b ⟨2 * i % 256, Nat.mod_lt _ (by norm_num)⟩
    + 2 * b ⟨(2 * i + 1) % 256, Nat.mod_lt _ (by norm_num)⟩

/-- Pairing identity: the window sum of `b` over `m` windows is the bit sum over
the first `2m` bits. -/
theorem window_digit_sum_aux (b : Nat → Nat) :
    ∀ m : Nat, (∑ i ∈ Finset.range m, (b (2 * i) + 2 * b (2 * i + 1)) * 4 ^ i)
      = ∑ j ∈ Finset.range (2 * m), 2 ^ j * b j := by
  intro m
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih,
      show 2 * (k + 1) = 2 * k + 1 + 1 from by omega,
      Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 : 2 ^ (2 * k) = 4 ^ k := by
      rw [show (2:Nat) ^ (2 * k) = (2 ^ 2) ^ k from by rw [Nat.pow_mul],
        show (2:Nat) ^ 2 = 4 from rfl]
    have h2 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
      rw [Nat.pow_succ, h1, Nat.mul_comm]
    rw [h1, h2]
    have h3 : (b (2 * k) + 2 * b (2 * k + 1)) * 4 ^ k
        = 4 ^ k * b (2 * k) + 2 * 4 ^ k * b (2 * k + 1) := by
      rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (b (2 * k)) (4 ^ k),
        Nat.mul_comm (b (2 * k + 1)) (4 ^ k), Nat.mul_assoc]
    rw [h3]
    omega

/-- **Digest window decomposition.**  For any 256-bit vector `b`, the window
digits `b_{2i} + 2·b_{2i+1}` recompose to the little-endian natural. -/
theorem window_digit_sum (b : Fin 256 → Nat) :
    (∑ i ∈ Finset.range 128, windowDigit b i * 4 ^ i) = leNat b := by
  simp only [windowDigit]
  rw [window_digit_sum_aux (fun j => b ⟨j % 256, Nat.mod_lt _ (by norm_num)⟩) 128,
    show 2 * 128 = 256 from rfl, leNat_eq_sum_range]

end StandardECDSA.Math
