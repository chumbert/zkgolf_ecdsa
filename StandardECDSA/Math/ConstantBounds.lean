/-
# Constant bounds: zero runs and the gated comparison

The standard circuit's `overflow` branch needs a *conditional* comparison: it must
assert `r < p - n` only when `overflow = 1`, at the cost of one product per row.
The plan's construction uses the maximal zero runs of `(p - n) - 1` and of
`n - 1`.

This module

* defines the zero-run extraction on the 256-bit little-endian representation;
* certifies the actual run lists of `n - 1` and `p - n - 1` in the kernel
  (`decide`), confirming the plan's count of 34 runs each;
* proves the basic bit-bound lemma that a number whose bits vanish above
  position `k` is below `2^k`.

The soundness/completeness of the *gated comparator rows* themselves is task T06
and depends on the circuit rows of T07; only the pure arithmetic is here.
-/

import StandardECDSA.Math.ScalarEncoding

namespace StandardECDSA.Math

open StandardECDSA

set_option maxRecDepth 100000

/-! ## Zero runs of the 256-bit representation -/

/-- Bit `i` (little-endian) of `m`. -/
def bitAt (m i : Nat) : Bool := (m / 2 ^ i) % 2 == 1

/-- Scan a little-endian bit list, collecting the lengths of maximal zero runs. -/
def runsAux : List Bool → Nat → List Nat → List Nat
  | [], cur, acc => if cur = 0 then acc else acc ++ [cur]
  | b :: bs, cur, acc =>
      if b then
        (if cur = 0 then runsAux bs 0 acc else runsAux bs 0 (acc ++ [cur]))
      else runsAux bs (cur + 1) acc

/-- The lengths of the maximal zero runs in the 256-bit representation of `m`. -/
def zeroRunLens (m : Nat) : List Nat :=
  runsAux ((List.range 256).map (bitAt m)) 0 []

/-- The maximal zero runs of `n - 1`, kernel-checked. -/
theorem zeroRunLens_n_sub_one :
    zeroRunLens (n - 1) =
      [4, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1,
        2, 2, 1, 32] := by
  decide

/-- The maximal zero runs of `(p - n) - 1`, kernel-checked. -/
theorem zeroRunLens_p_sub_n_sub_one :
    zeroRunLens (p - n - 1) =
      [1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 3, 3, 4, 1, 1, 4, 4, 1, 3, 1, 1, 2, 1, 1, 1, 5,
        2, 3, 4, 129] := by
  decide

/-- `n - 1` has exactly 34 maximal zero runs, as the plan asserts. -/
theorem zero_runs_n_minus_one : (zeroRunLens (n - 1)).length = 34 := by
  rw [zeroRunLens_n_sub_one]; decide

/-- `(p - n) - 1` has exactly 34 maximal zero runs, as the plan asserts. -/
theorem zero_runs_p_minus_n_minus_one : (zeroRunLens (p - n - 1)).length = 34 := by
  rw [zeroRunLens_p_sub_n_sub_one]; decide

/-- The total number of zero bits in `n - 1` is 90. -/
theorem zero_bits_n_minus_one : (zeroRunLens (n - 1)).sum = 90 := by
  rw [zeroRunLens_n_sub_one]; decide

/-- The total number of zero bits in `(p - n) - 1` is 198. -/
theorem zero_bits_p_minus_n_minus_one : (zeroRunLens (p - n - 1)).sum = 198 := by
  rw [zeroRunLens_p_sub_n_sub_one]; decide

/-! ## Bit bounds -/

/-- If every bit of `m` at position `≥ k` is zero, then `m < 2^k`. -/
theorem lt_two_pow_of_bits_zero (m k : Nat) (h : m / 2 ^ k = 0) : m < 2 ^ k := by
  by_contra hlt
  push_neg at hlt
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have : 0 < m / 2 ^ k := Nat.div_pos hlt hpos
  omega

/-- A 256-bit number is below `2^256`. -/
theorem lt_two_pow_256_of_bits_zero (m : Nat) (h : m / 2 ^ 256 = 0) : m < 2 ^ 256 :=
  lt_two_pow_of_bits_zero m 256 h

end StandardECDSA.Math
