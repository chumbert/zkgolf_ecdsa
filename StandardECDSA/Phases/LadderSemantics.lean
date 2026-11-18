/-
# Joint-ladder phase: group semantics

Plan §5 signed-offset ladder invariant:

```text
C_0 = O
C_(j+1) = [2]C_j + T_j
T_j = [rBit[255-j]]Q + [tBit[255-j]]R + σ_j·[3]H,   σ_j = -1 (even j), +1 (odd j)
```

After 256 steps the represented point is `[r]Q + [t]R - H`; the final `elmTo`
asserts it equals `-ep`, giving `[E]G + [r]Q + [t]R = O` after cancelling `H`.

This module supplies the offset-generic row-level soundness of `elm` / `elmTo`
(analogues of `affAdd_sound` in `Phases/TableSemantics.lean`), the row-level
soundness of `mux4W`, and the group-level ladder invariant.

Task T15.
-/

import StandardECDSA.Phases.TableSemantics
import StandardECDSA.Phases.JointLadder
import StandardECDSA.Phases.FixedBaseSemantics

namespace StandardECDSA.Phases

open StandardECDSA.Gadgets
open StandardECDSA.Math
open WeierstrassCurve

/-! ## Offset-generic row-level soundness of `elm` and `elmTo` -/

/-- The six rows of `elm p q` at offset `n` give `2 • p + q`, with the output at
`n + 4`, `n + 5`.  The distinct-`x` guard is *derived* from the enforced inverse
row, and the second denominator is derived from the curve equations — no extra
hypothesis is needed. -/
theorem elm_sound (env : Environment Fp) (p q : Pt) (n : Nat)
    (hA : NS (Expression.eval env p.1) (Expression.eval env p.2))
    (hB : NS (Expression.eval env q.1) (Expression.eval env q.2))
    (h : ConstraintsHold.Soundness env ((elm p q).operations n)) :
    ∃ hR : NS (env.get (n + 4)) (env.get (n + 5)),
      Affine.Point.some (env.get (n + 4)) (env.get (n + 5)) hR
        = 2 • Affine.Point.some (Expression.eval env p.1) (Expression.eval env p.2) hA
          + Affine.Point.some (Expression.eval env q.1) (Expression.eval env q.2) hB := by
  simp only [elm, elmCore, nonzero, circuit_norm, pm] at h
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := h
  simp only [eval_cst, eval_sc] at r1 r2 r3 r4 r5 r6
  rw [show n + 1 + 1 + 1 = n + 3 from by omega] at r4 r5 r6
  rw [show n + 1 + 1 = n + 2 from by omega] at r3 r4 r5
  rw [show n + 4 + 1 = n + 5 from by omega] at r6
  refine elmEqs_group #v[Expression.eval env p.1, Expression.eval env p.2,
    Expression.eval env q.1, Expression.eval env q.2] (env.get (n + 4), env.get (n + 5))
    hA hB ⟨env.get n, env.get (n + 1), env.get (n + 2), env.get (n + 3),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (Expression.eval env q.1 - Expression.eval env p.1) * env.get n = 1
    linear_combination r1
  · show (Expression.eval env q.1 - Expression.eval env p.1) * env.get (n + 1)
      = Expression.eval env q.2 - Expression.eval env p.2
    linear_combination r2
  · show env.get (n + 1) * env.get (n + 1) - Expression.eval env p.1
      - Expression.eval env q.1 - env.get (n + 2) = 0
    linear_combination r3
  · show (env.get (n + 1) + env.get (n + 3)) * (Expression.eval env p.1 - env.get (n + 2))
      - 2 * Expression.eval env p.2 = 0
    linear_combination r4
  · show env.get (n + 3) * env.get (n + 3) - Expression.eval env p.1
      - env.get (n + 2) - env.get (n + 4) = 0
    linear_combination r5
  · show env.get (n + 3) * (Expression.eval env p.1 - env.get (n + 4))
      - Expression.eval env p.2 - env.get (n + 5) = 0
    linear_combination r6

/-- The six rows of `elmTo p q target` at offset `n` assert `2 • p + q = target`
against the already supplied target. -/
theorem elmTo_sound (env : Environment Fp) (p q target : Pt) (n : Nat)
    (hA : NS (Expression.eval env p.1) (Expression.eval env p.2))
    (hB : NS (Expression.eval env q.1) (Expression.eval env q.2))
    (hT : NS (Expression.eval env target.1) (Expression.eval env target.2))
    (h : ConstraintsHold.Soundness env ((elmTo p q target).operations n)) :
    2 • Affine.Point.some (Expression.eval env p.1) (Expression.eval env p.2) hA
        + Affine.Point.some (Expression.eval env q.1) (Expression.eval env q.2) hB
      = Affine.Point.some (Expression.eval env target.1) (Expression.eval env target.2) hT := by
  simp only [elmTo, elmCore, nonzero, circuit_norm, pm] at h
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := h
  simp only [eval_cst, eval_sc] at r1 r2 r3 r4 r5 r6
  rw [show n + 1 + 1 + 1 = n + 3 from by omega] at r4 r5 r6
  rw [show n + 1 + 1 = n + 2 from by omega] at r3 r4 r5
  have hEqs : elmEqs #v[Expression.eval env p.1, Expression.eval env p.2,
      Expression.eval env q.1, Expression.eval env q.2]
      (Expression.eval env target.1, Expression.eval env target.2) := by
    refine ⟨env.get n, env.get (n + 1), env.get (n + 2), env.get (n + 3),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (Expression.eval env q.1 - Expression.eval env p.1) * env.get n = 1
      linear_combination r1
    · show (Expression.eval env q.1 - Expression.eval env p.1) * env.get (n + 1)
        = Expression.eval env q.2 - Expression.eval env p.2
      linear_combination r2
    · show env.get (n + 1) * env.get (n + 1) - Expression.eval env p.1
        - Expression.eval env q.1 - env.get (n + 2) = 0
      linear_combination r3
    · show (env.get (n + 1) + env.get (n + 3)) * (Expression.eval env p.1 - env.get (n + 2))
        - 2 * Expression.eval env p.2 = 0
      linear_combination r4
    · show env.get (n + 3) * env.get (n + 3) - Expression.eval env p.1
        - env.get (n + 2) - Expression.eval env target.1 = 0
      linear_combination r5
    · show env.get (n + 3) * (Expression.eval env p.1 - Expression.eval env target.1)
        - Expression.eval env p.2 - Expression.eval env target.2 = 0
      linear_combination r6
  obtain ⟨hR, hval⟩ := elmEqs_group _ _ hA hB hEqs
  exact hval.symm.trans (some_congr rfl rfl hR hT)

/-! ## Row-level soundness of `mux4W` -/

/-- The six rows of `mux4W` at offset `n` select the table entry indexed by
`b0 + 2·b1` at Boolean selectors. -/
theorem mux4W_sound (env : Environment Fp) (b0 b1 : E) (p0 p1 p2 p3 : Pt) (n : Nat)
    (hb0 : Expression.eval env b0 = 0 ∨ Expression.eval env b0 = 1)
    (hb1 : Expression.eval env b1 = 0 ∨ Expression.eval env b1 = 1)
    (h : ConstraintsHold.Soundness env ((mux4W b0 b1 p0 p1 p2 p3).operations n)) :
    Expression.eval env ((mux4W b0 b1 p0 p1 p2 p3).output n).1
        = (if Expression.eval env b0 = 0 then
            (if Expression.eval env b1 = 0 then Expression.eval env p0.1
              else Expression.eval env p2.1)
          else (if Expression.eval env b1 = 0 then Expression.eval env p1.1
            else Expression.eval env p3.1))
      ∧ Expression.eval env ((mux4W b0 b1 p0 p1 p2 p3).output n).2
        = (if Expression.eval env b0 = 0 then
            (if Expression.eval env b1 = 0 then Expression.eval env p0.2
              else Expression.eval env p2.2)
          else (if Expression.eval env b1 = 0 then Expression.eval env p1.2
            else Expression.eval env p3.2)) := by
  simp only [mux4W, selW, circuit_norm, pm] at h
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  rw [show n + 1 + 1 + 1 + 1 + 1 = n + 5 from by omega] at h5
  rw [show n + 1 + 1 + 1 + 1 = n + 4 from by omega] at h4 h5
  rw [show n + 1 + 1 + 1 = n + 3 from by omega] at h3 h5
  rw [show n + 1 + 1 = n + 2 from by omega] at h2
  have h0' : Expression.eval env (pm b0 (p1.1 - p0.1) - Expression.var (F := Fp) ⟨n⟩) = 0 := by
    simp only [pm, circuit_norm]
    linear_combination h0
  have h1' : Expression.eval env (pm b0 (p3.1 - p2.1) - Expression.var (F := Fp) ⟨n + 1⟩) = 0 := by
    simp only [pm, circuit_norm]
    linear_combination h1
  have h2' : Expression.eval env
      (pm b1 ((p2.1 + Expression.var (F := Fp) ⟨n + 1⟩)
        - (p0.1 + Expression.var (F := Fp) ⟨n⟩)) - Expression.var (F := Fp) ⟨n + 2⟩) = 0 := by
    simp only [pm, circuit_norm]
    linear_combination h2
  have h3' : Expression.eval env (pm b0 (p1.2 - p0.2) - Expression.var (F := Fp) ⟨n + 3⟩) = 0 := by
    simp only [pm, circuit_norm]
    linear_combination h3
  have h4' : Expression.eval env (pm b0 (p3.2 - p2.2) - Expression.var (F := Fp) ⟨n + 4⟩) = 0 := by
    simp only [pm, circuit_norm]
    linear_combination h4
  have h5' : Expression.eval env
      (pm b1 ((p2.2 + Expression.var (F := Fp) ⟨n + 4⟩)
        - (p0.2 + Expression.var (F := Fp) ⟨n + 3⟩)) - Expression.var (F := Fp) ⟨n + 5⟩) = 0 := by
    simp only [pm, circuit_norm]
    linear_combination h5
  obtain ⟨e1, e2⟩ := mux4W_eval env b0 b1 p0 p1 p2 p3 n h0' h1' h2' h3' h4' h5'
  rw [e1, e2, mux4Val_bits _ _ _ _ _ _ hb0 hb1]
  by_cases hb : Expression.eval env b0 = 0 <;>
    by_cases hb' : Expression.eval env b1 = 0 <;> simp [hb, hb']

/-! ## The signed-offset ladder invariant (plan §5) -/

/-- The offset sign at ladder step `j`: `+1` for even `j`, `-1` for odd `j`. -/
def sigma (j : Nat) : ℤ := (-1) ^ j

/-- The `r`-bit read at ladder step `j` (MSB-first consumption: index `255 - j`). -/
noncomputable def rBitAt (env : Environment Fp) (rb : Vector E 256) (j : Nat) : ℤ :=
  if Expression.eval env (rb.get ⟨255 - j, by omega⟩) = 1 then 1 else 0

/-- The `t`-bit read at ladder step `j`. -/
noncomputable def tBitAt (env : Environment Fp) (sb : Vector E 256) (j : Nat) : ℤ :=
  if Expression.eval env (sb.get ⟨255 - j, by omega⟩) = 1 then 1 else 0

/-- The group point selected at ladder step `j`: `σ_j·[3]H + b0·Q + b1·R`. -/
noncomputable def Tpt (Hpt Qpt Rpt : Affine.Point Wp) (env : Environment Fp)
    (rb sb : Vector E 256) (j : Nat) : Affine.Point Wp :=
  (3 * sigma j) • Hpt + rBitAt env rb j • Qpt + tBitAt env sb j • Rpt

/-- The ladder's represented group point after `j` steps:
`C_0 = -H`, `C_(j+1) = [2]C_j + T_j`. -/
noncomputable def ladAcc (Hpt Qpt Rpt : Affine.Point Wp) (env : Environment Fp)
    (rb sb : Vector E 256) : Nat → Affine.Point Wp
  | 0 => -Hpt
  | (j + 1) => (2 : ℤ) • ladAcc Hpt Qpt Rpt env rb sb j + Tpt Hpt Qpt Rpt env rb sb j

/-- The `H`-part of the ladder accumulator. -/
noncomputable def ladAccH (Hpt : Affine.Point Wp) : Nat → Affine.Point Wp
  | 0 => -Hpt
  | (j + 1) => (2 : ℤ) • ladAccH Hpt j + (3 * sigma j) • Hpt

/-- The `Q`-part of the ladder accumulator. -/
noncomputable def ladAccQ (Qpt : Affine.Point Wp) (env : Environment Fp)
    (rb : Vector E 256) : Nat → Affine.Point Wp
  | 0 => 0
  | (j + 1) => (2 : ℤ) • ladAccQ Qpt env rb j + rBitAt env rb j • Qpt

/-- The `R`-part of the ladder accumulator. -/
noncomputable def ladAccR (Rpt : Affine.Point Wp) (env : Environment Fp)
    (sb : Vector E 256) : Nat → Affine.Point Wp
  | 0 => 0
  | (j + 1) => (2 : ℤ) • ladAccR Rpt env sb j + tBitAt env sb j • Rpt

/-- The ladder invariant: the accumulator is the represented group point. -/
noncomputable def ladInv (Hpt Qpt Rpt : Affine.Point Wp) (env : Environment Fp)
    (rb sb : Vector E 256) (j : Nat) (acc : Pt) : Prop :=
  ∃ hns : NS (Expression.eval env acc.1) (Expression.eval env acc.2),
    Affine.Point.some (Expression.eval env acc.1) (Expression.eval env acc.2) hns
      = ladAcc Hpt Qpt Rpt env rb sb j

/-- The accumulator splits into its `H`, `Q` and `R` parts. -/
theorem ladAcc_split (Hpt Qpt Rpt : Affine.Point Wp) (env : Environment Fp)
    (rb sb : Vector E 256) (j : Nat) :
    ladAcc Hpt Qpt Rpt env rb sb j
      = ladAccH Hpt j + ladAccQ Qpt env rb j + ladAccR Rpt env sb j := by
  induction j with
  | zero => simp only [ladAcc, ladAccH, ladAccQ, ladAccR]; abel
  | succ j ih =>
    simp only [ladAcc, ladAccH, ladAccQ, ladAccR, Tpt, ih]
    abel

/-- The `H`-part alternates: `ladAccH j = (-1)^(j+1) • H`. -/
theorem ladAccH_eq (Hpt : Affine.Point Wp) (j : Nat) :
    ladAccH Hpt j = ((-1 : ℤ) ^ (j + 1)) • Hpt := by
  induction j with
  | zero => simp [ladAccH]
  | succ j ih =>
    rw [ladAccH, ih, sigma]
    rw [show (2 : ℤ) • (((-1 : ℤ) ^ (j + 1)) • Hpt)
        = ((2 : ℤ) * (-1 : ℤ) ^ (j + 1)) • Hpt
        from (mul_zsmul Hpt 2 ((-1 : ℤ) ^ (j + 1))).symm]
    rw [← add_zsmul]
    congr 1
    ring

/-- The little-endian weighted sum of the `r`-bits consumed so far. -/
noncomputable def bitSum (env : Environment Fp) (rb : Vector E 256) (j : Nat) : ℤ :=
  ∑ i ∈ Finset.range j, (2 : ℤ) ^ (j - 1 - i) * rBitAt env rb i

theorem bitSum_succ (env : Environment Fp) (rb : Vector E 256) (j : Nat) :
    bitSum env rb (j + 1) = 2 * bitSum env rb j + rBitAt env rb j := by
  simp only [bitSum, Finset.sum_range_succ]
  have h : (∑ i ∈ Finset.range j, (2 : ℤ) ^ (j + 1 - 1 - i) * rBitAt env rb i)
      = 2 * ∑ i ∈ Finset.range j, (2 : ℤ) ^ (j - 1 - i) * rBitAt env rb i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Finset.mem_range] at hi
    rw [show j + 1 - 1 - i = (j - 1 - i) + 1 from by omega, pow_succ]
    ring
  rw [h, show j + 1 - 1 - j = 0 from by omega, pow_zero, one_mul]

/-- The `Q`-part is the weighted bit sum times `Q`. -/
theorem ladAccQ_eq (Qpt : Affine.Point Wp) (env : Environment Fp)
    (rb : Vector E 256) (j : Nat) :
    ladAccQ Qpt env rb j = bitSum env rb j • Qpt := by
  induction j with
  | zero => simp [ladAccQ, bitSum]
  | succ j ih =>
    rw [ladAccQ, ih, bitSum_succ, add_zsmul]
    rw [show (2 : ℤ) • (bitSum env rb j • Qpt) = ((2 : ℤ) * bitSum env rb j) • Qpt
      from (mul_zsmul Qpt 2 (bitSum env rb j)).symm]

/-- The little-endian weighted sum of the `t`-bits consumed so far. -/
noncomputable def bitSumT (env : Environment Fp) (sb : Vector E 256) (j : Nat) : ℤ :=
  ∑ i ∈ Finset.range j, (2 : ℤ) ^ (j - 1 - i) * tBitAt env sb i

theorem bitSumT_succ (env : Environment Fp) (sb : Vector E 256) (j : Nat) :
    bitSumT env sb (j + 1) = 2 * bitSumT env sb j + tBitAt env sb j := by
  simp only [bitSumT, Finset.sum_range_succ]
  have h : (∑ i ∈ Finset.range j, (2 : ℤ) ^ (j + 1 - 1 - i) * tBitAt env sb i)
      = 2 * ∑ i ∈ Finset.range j, (2 : ℤ) ^ (j - 1 - i) * tBitAt env sb i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Finset.mem_range] at hi
    rw [show j + 1 - 1 - i = (j - 1 - i) + 1 from by omega, pow_succ]
    ring
  rw [h, show j + 1 - 1 - j = 0 from by omega, pow_zero, one_mul]

/-- The `R`-part is the weighted bit sum times `R`. -/
theorem ladAccR_eq (Rpt : Affine.Point Wp) (env : Environment Fp)
    (sb : Vector E 256) (j : Nat) :
    ladAccR Rpt env sb j = bitSumT env sb j • Rpt := by
  induction j with
  | zero => simp [ladAccR, bitSumT]
  | succ j ih =>
    rw [ladAccR, ih, bitSumT_succ, add_zsmul]
    rw [show (2 : ℤ) • (bitSumT env sb j • Rpt) = ((2 : ℤ) * bitSumT env sb j) • Rpt
      from (mul_zsmul Rpt 2 (bitSumT env sb j)).symm]

/-! ## The bit sums are the little-endian scalars -/

/-- A Boolean field value read as an integer bit. -/
theorem rBitAt_eq (env : Environment Fp) (rb : Vector E 256)
    (hb : ∀ k : Fin 256, Expression.eval env (rb.get k) = 0 ∨ Expression.eval env (rb.get k) = 1)
    (i : Nat) :
    rBitAt env rb i = ((Expression.eval env (rb.get ⟨255 - i, by omega⟩)).val : ℤ) := by
  rw [rBitAt]
  rcases hb ⟨255 - i, by omega⟩ with h | h
  · rw [if_neg (by rw [h]; exact zero_ne_one), h]
    simp [ZMod.val_zero]
  · rw [if_pos h, h]
    simp [ZMod.val_one]

theorem tBitAt_eq (env : Environment Fp) (sb : Vector E 256)
    (hb : ∀ k : Fin 256, Expression.eval env (sb.get k) = 0 ∨ Expression.eval env (sb.get k) = 1)
    (i : Nat) :
    tBitAt env sb i = ((Expression.eval env (sb.get ⟨255 - i, by omega⟩)).val : ℤ) := by
  rw [tBitAt]
  rcases hb ⟨255 - i, by omega⟩ with h | h
  · rw [if_neg (by rw [h]; exact zero_ne_one), h]
    simp [ZMod.val_zero]
  · rw [if_pos h, h]
    simp [ZMod.val_one]

/-- The 256-step weighted `r`-bit sum is the little-endian scalar `r`. -/
theorem bitSum_256 (env : Environment Fp) (rb : Vector E 256)
    (hb : ∀ k : Fin 256, Expression.eval env (rb.get k) = 0 ∨ Expression.eval env (rb.get k) = 1) :
    bitSum env rb 256
      = (leNat (fun k : Fin 256 => (Expression.eval env (rb.get k)).val) : ℤ) := by
  have hbit : ∀ i : Nat, rBitAt env rb i
      = ((Expression.eval env (rb.get ⟨255 - i, by omega⟩)).val : ℤ) := rBitAt_eq env rb hb
  simp only [bitSum, hbit]
  rw [leNat_eq_sum_range, Nat.cast_sum]
  have hL : (∑ x ∈ Finset.range 256,
      2 ^ (256 - 1 - x) * ((Expression.eval env (rb.get ⟨255 - x, by omega⟩)).val : ℤ))
      = ∑ x ∈ Finset.range 256,
      2 ^ (256 - 1 - x)
        * ((Expression.eval env (rb.get ⟨(256 - 1 - x) % 256,
            Nat.mod_lt _ (by norm_num)⟩)).val : ℤ) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [Finset.mem_range] at hx
    have hfin : (⟨255 - x, by omega⟩ : Fin 256)
        = ⟨(256 - 1 - x) % 256, Nat.mod_lt _ (by norm_num)⟩ := by
      ext
      simp only [Fin.val_mk]
      omega
    rw [hfin]
  rw [hL, Finset.sum_range_reflect
    (fun k => (2 : ℤ) ^ k
      * ((Expression.eval env (rb.get ⟨k % 256, Nat.mod_lt _ (by norm_num)⟩)).val : ℤ)) 256]
  push_cast
  rfl

/-- The 256-step weighted `t`-bit sum is the little-endian scalar `t`. -/
theorem bitSumT_256 (env : Environment Fp) (sb : Vector E 256)
    (hb : ∀ k : Fin 256, Expression.eval env (sb.get k) = 0 ∨ Expression.eval env (sb.get k) = 1) :
    bitSumT env sb 256
      = (leNat (fun k : Fin 256 => (Expression.eval env (sb.get k)).val) : ℤ) := by
  have hbit : ∀ i : Nat, tBitAt env sb i
      = ((Expression.eval env (sb.get ⟨255 - i, by omega⟩)).val : ℤ) := tBitAt_eq env sb hb
  simp only [bitSumT, hbit]
  rw [leNat_eq_sum_range, Nat.cast_sum]
  have hL : (∑ x ∈ Finset.range 256,
      2 ^ (256 - 1 - x) * ((Expression.eval env (sb.get ⟨255 - x, by omega⟩)).val : ℤ))
      = ∑ x ∈ Finset.range 256,
      2 ^ (256 - 1 - x)
        * ((Expression.eval env (sb.get ⟨(256 - 1 - x) % 256,
            Nat.mod_lt _ (by norm_num)⟩)).val : ℤ) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [Finset.mem_range] at hx
    have hfin : (⟨255 - x, by omega⟩ : Fin 256)
        = ⟨(256 - 1 - x) % 256, Nat.mod_lt _ (by norm_num)⟩ := by
      ext
      simp only [Fin.val_mk]
      omega
    rw [hfin]
  rw [hL, Finset.sum_range_reflect
    (fun k => (2 : ℤ) ^ k
      * ((Expression.eval env (sb.get ⟨k % 256, Nat.mod_lt _ (by norm_num)⟩)).val : ℤ)) 256]
  push_cast
  rfl

/-- **Sign cancellation (plan §5).**  After 256 steps the ladder represents
`[r]Q + [t]R - H`: the alternating `±3H` offsets cancel the `[2^256]H` term and
leave exactly `-H`. -/
theorem ladAcc_256 (Hpt Qpt Rpt : Affine.Point Wp) (env : Environment Fp)
    (rb sb : Vector E 256)
    (hb : ∀ k : Fin 256, Expression.eval env (rb.get k) = 0 ∨ Expression.eval env (rb.get k) = 1)
    (hb' : ∀ k : Fin 256, Expression.eval env (sb.get k) = 0 ∨ Expression.eval env (sb.get k) = 1) :
    ladAcc Hpt Qpt Rpt env rb sb 256
      = (leNat (fun k : Fin 256 => (Expression.eval env (rb.get k)).val) : ℤ) • Qpt
        + (leNat (fun k : Fin 256 => (Expression.eval env (sb.get k)).val) : ℤ) • Rpt - Hpt := by
  rw [ladAcc_split, ladAccH_eq, ladAccQ_eq, ladAccR_eq, bitSum_256 env rb hb,
    bitSumT_256 env sb hb']
  rw [show ((-1 : ℤ) ^ (256 + 1)) = -1 from by norm_num]
  rw [neg_one_zsmul]
  abel

/-! ## Table selection at Boolean bits -/

/-- At Boolean selectors the four-way table selection is the nested `if` used by
`mux4W_sound`. -/
theorem sel_eq_of_bits (t : Tables) (j : Nat) (v w : Fp)
    (hv : v = 0 ∨ v = 1) (hw : w = 0 ∨ w = 1) :
    t.sel j (v == 1) (w == 1)
      = if v = 0 then (if w = 0 then t.x0 j else t.x2 j)
        else (if w = 0 then t.x1 j else t.x3 j) := by
  have h0 : ((0 : Fp) == 1) = false := by decide
  have h1 : ((1 : Fp) == 1) = true := by decide
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;>
    simp [Tables.sel, h0, h1]

/-- A Boolean field value read as an integer bit agrees with the `== 1` test. -/
theorem ite_beq_one (v : Fp) (hv : v = 0 ∨ v = 1) :
    (if (v == 1) then (1 : ℤ) else 0) = if v = 1 then 1 else 0 := by
  have h0 : ((0 : Fp) == 1) = false := by decide
  have h1 : ((1 : Fp) == 1) = true := by decide
  rcases hv with rfl | rfl <;> simp [h0, h1]

/-- The `mux4W` of ladder step `j` selects the group point `T_j`.

The table hypothesis is stated in the *nested-`if`* form produced by
`mux4W_sound`, so no `Tables.sel` conversion is needed here; the caller
discharges it from `Tables.Spec` via `sel_eq_of_bits`. -/
theorem mux4W_Tpt (env : Environment Fp) (Hpt Qpt Rpt : Affine.Point Wp)
    (tables : Tables) (rb sb : Vector E 256) (j : Nat) (hj : j < 256) (n : Nat)
    (hb : ∀ k : Fin 256, Expression.eval env (rb.get k) = 0 ∨ Expression.eval env (rb.get k) = 1)
    (hb' : ∀ k : Fin 256, Expression.eval env (sb.get k) = 0 ∨ Expression.eval env (sb.get k) = 1)
    (htab : ∀ (j : Nat) (hj : j < 256) (v w : Fp), (v = 0 ∨ v = 1) → (w = 0 ∨ w = 1) →
      ∃ hns : NS (if v = 0 then
            (if w = 0 then Expression.eval env (tables.x0 j).1
              else Expression.eval env (tables.x2 j).1)
          else (if w = 0 then Expression.eval env (tables.x1 j).1
            else Expression.eval env (tables.x3 j).1))
          (if v = 0 then
            (if w = 0 then Expression.eval env (tables.x0 j).2
              else Expression.eval env (tables.x2 j).2)
          else (if w = 0 then Expression.eval env (tables.x1 j).2
            else Expression.eval env (tables.x3 j).2)),
        Affine.Point.some _ _ hns
          = (3 * sigma j) • Hpt + (if v = 1 then (1 : ℤ) else 0) • Qpt
            + (if w = 1 then (1 : ℤ) else 0) • Rpt)
    (h : ConstraintsHold.Soundness env
      ((mux4W (rb.get ⟨255 - j, by omega⟩) (sb.get ⟨255 - j, by omega⟩)
        (tables.x0 j) (tables.x1 j) (tables.x2 j) (tables.x3 j)).operations n)) :
    ∃ hns : NS (Expression.eval env
        ((mux4W (rb.get ⟨255 - j, by omega⟩) (sb.get ⟨255 - j, by omega⟩)
          (tables.x0 j) (tables.x1 j) (tables.x2 j) (tables.x3 j)).output n).1)
        (Expression.eval env
        ((mux4W (rb.get ⟨255 - j, by omega⟩) (sb.get ⟨255 - j, by omega⟩)
          (tables.x0 j) (tables.x1 j) (tables.x2 j) (tables.x3 j)).output n).2),
      Affine.Point.some _ _ hns = Tpt Hpt Qpt Rpt env rb sb j := by
  obtain ⟨e1, e2⟩ := mux4W_sound env _ _ _ _ _ _ n
    (hb ⟨255 - j, by omega⟩) (hb' ⟨255 - j, by omega⟩) h
  obtain ⟨hns, hval⟩ := htab j hj
    (Expression.eval env (rb.get ⟨255 - j, by omega⟩))
    (Expression.eval env (sb.get ⟨255 - j, by omega⟩))
    (hb ⟨255 - j, by omega⟩) (hb' ⟨255 - j, by omega⟩)
  have hns' : NS (Expression.eval env
      ((mux4W (rb.get ⟨255 - j, by omega⟩) (sb.get ⟨255 - j, by omega⟩)
        (tables.x0 j) (tables.x1 j) (tables.x2 j) (tables.x3 j)).output n).1)
      (Expression.eval env
      ((mux4W (rb.get ⟨255 - j, by omega⟩) (sb.get ⟨255 - j, by omega⟩)
        (tables.x0 j) (tables.x1 j) (tables.x2 j) (tables.x3 j)).output n).2) :=
    ns_congr e1 e2 hns
  refine ⟨hns', ?_⟩
  refine (some_congr e1 e2 hns' hns).trans ?_
  refine hval.trans ?_
  simp only [Tpt, rBitAt, tBitAt]

/-- **Per-step row constraints of a `foldlRange` loop, from an abstracted
operation list.**

The loop's operation list is passed as an opaque variable `F` together with the
equation `hF` identifying it.  This matters: `Circuit.operations` is
`@[reducible]`, so any defeq check that mentions the *concrete* 255-step fold
unfolds the whole `Fin.foldl` and exceeds the recursion budget.  With `F` a
variable the check is purely syntactic. -/
theorem soundness_foldlRange_of_eq (env : Environment Fp) {m : Nat} {β : Type} [Inhabited β]
    {init : β} {body : β → Fin m → Circuit Fp β}
    {constant : Circuit.ConstantLength fun (t : β × Fin m) => body t.1 t.2} {n : Nat}
    {F : Operations Fp} (hF : F = (Circuit.foldlRange m init body constant).operations n)
    (h : F.forAllNoOffset (soundnessCond env)) :
    ∀ i : Fin m,
      ((body (Circuit.FoldlM.foldlAcc n (Vector.finRange m) body init i) i).operations
        (n + i * (body default i).localLength)).forAllNoOffset (soundnessCond env) := by
  subst hF
  exact soundness_foldlRange env h

/-- `foldlAcc` for the ladder body, with the constant local length `12`. -/
theorem foldlAcc_eq_ladder (tables : Tables) (rb sb : Vector E 256)
    (init : Pt) (n : Nat) (k : Nat) (hk : k < 255) :
    Circuit.FoldlM.foldlAcc n (Vector.finRange 255) (jointLadderBody tables rb sb) init ⟨k, hk⟩
      = Fin.foldl k (fun acc (i : Fin k) =>
          (jointLadderBody tables rb sb acc ⟨i.val, by omega⟩).output (n + i.val * 12)) init := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]
  congr 1

set_option linter.constructorNameAsVariable false in
/-- **Joint-ladder phase spec (plan §5).**

From *any* satisfying assignment of the ladder's rows, the final `elmTo`
assertion forces the target to be the represented point `[r]Q + [t]R - H`.  The
only extra hypotheses are the Booleanity of the two scalar bit vectors, the
initial accumulator being `-H`, the shifted-table contract, and the
distinct-`x` conditions of the 256 `elm`/`elmTo` steps (supplied by the global
offset theorem).

The 255 returning steps are handled by `fin_foldl_inv'` with the signed-offset
prefix invariant `ladInv`; the final step is the `elmTo` assertion to the
target.  Sign cancellation is `ladAcc_256`. -/
theorem jointLadder_spec (env : Environment Fp) (Hpt Qpt Rpt : Affine.Point Wp)
    (acc0 : Pt) (tables : Tables) (rb sb : Vector E 256) (target : Pt) (n : Nat)
    (hacc0 : ∃ hns : NS (Expression.eval env acc0.1) (Expression.eval env acc0.2),
      Affine.Point.some (Expression.eval env acc0.1) (Expression.eval env acc0.2) hns = -Hpt)
    (hb : ∀ k : Fin 256, Expression.eval env (rb.get k) = 0 ∨ Expression.eval env (rb.get k) = 1)
    (hb' : ∀ k : Fin 256, Expression.eval env (sb.get k) = 0 ∨ Expression.eval env (sb.get k) = 1)
    (htab : ∀ (j : Nat) (hj : j < 256) (v w : Fp), (v = 0 ∨ v = 1) → (w = 0 ∨ w = 1) →
      ∃ hns : NS (if v = 0 then
            (if w = 0 then Expression.eval env (tables.x0 j).1
              else Expression.eval env (tables.x2 j).1)
          else (if w = 0 then Expression.eval env (tables.x1 j).1
            else Expression.eval env (tables.x3 j).1))
          (if v = 0 then
            (if w = 0 then Expression.eval env (tables.x0 j).2
              else Expression.eval env (tables.x2 j).2)
          else (if w = 0 then Expression.eval env (tables.x1 j).2
            else Expression.eval env (tables.x3 j).2)),
        Affine.Point.some _ _ hns
          = (3 * sigma j) • Hpt + (if v = 1 then (1 : ℤ) else 0) • Qpt
            + (if w = 1 then (1 : ℤ) else 0) • Rpt)
    (hT : NS (Expression.eval env target.1) (Expression.eval env target.2))
    (hc : ConstraintsHold.Soundness env ((jointLadder acc0 tables rb sb target).operations n)) :
    ∃ hns : NS (Expression.eval env target.1) (Expression.eval env target.2),
      Affine.Point.some (Expression.eval env target.1) (Expression.eval env target.2) hns
        = (leNat (fun k : Fin 256 => (Expression.eval env (rb.get k)).val) : ℤ) • Qpt
          + (leNat (fun k : Fin 256 => (Expression.eval env (sb.get k)).val) : ℤ) • Rpt - Hpt := by
  -- Split the phase into the 255-step fold and the final step.
  --
  -- `Circuit.operations` is `@[reducible]` and `List.append` matches on its
  -- first argument, so *any* defeq check mentioning `fold.operations n ++ …`
  -- unfolds the whole 255-step fold and exceeds the recursion budget.  We
  -- therefore split with `rw` (syntactic matching) rather than by applying
  -- `soundness_append`.
  rw [jointLadder_ops] at hc
  simp only [ConstraintsHold.Soundness] at hc
  rw [Operations.forAllNoOffset_append] at hc
  obtain ⟨hc1, hc2⟩ := hc
  rw [Circuit.foldlRange.forAllNoOffset] at hc1
  have hcl : ∀ i : Fin 255, (jointLadderBody tables rb sb default i).localLength = 12 := by
    intro i
    simp only [jointLadderBody, mux4W_localLength, elm_localLength, Circuit.localLength,
      Operations.append_localLength]
  -- the fold invariant
  have hinit : ladInv Hpt Qpt Rpt env rb sb 0 acc0 := hacc0
  have hstep : ∀ (j : Nat) (hj : j < 255),
      ladInv Hpt Qpt Rpt env rb sb j
        (Fin.foldl j (fun acc (i : Fin j) =>
          (jointLadderBody tables rb sb acc ⟨i.val, by omega⟩).output (n + i.val * 12)) acc0) →
      ladInv Hpt Qpt Rpt env rb sb (j + 1)
        ((jointLadderBody tables rb sb
          (Fin.foldl j (fun acc (i : Fin j) =>
            (jointLadderBody tables rb sb acc ⟨i.val, by omega⟩).output (n + i.val * 12)) acc0)
          ⟨j, hj⟩).output (n + j * 12)) := by
    intro j hj hacc
    obtain ⟨hns, hval⟩ := hacc
    have hcj := hc1 ⟨j, hj⟩
    rw [hcl ⟨j, hj⟩] at hcj
    rw [foldlAcc_eq_ladder tables rb sb acc0 n j hj] at hcj
    simp only [jointLadderBody_ops] at hcj
    rw [Operations.forAllNoOffset_append] at hcj
    obtain ⟨hm, he⟩ := hcj
    obtain ⟨hTm, hTval⟩ :=
      mux4W_Tpt env Hpt Qpt Rpt tables rb sb j (by omega : j < 256) (n + j * 12)
        hb hb' htab hm
    rw [jointLadderBody_out]
    simp only [ladInv]
    obtain ⟨hR, hRval⟩ := elm_sound env _ _ (n + j * 12 + 6) hns hTm he
    refine ⟨hR, ?_⟩
    refine hRval.trans ?_
    rw [hTval, hval]
    simp only [ladAcc]
    rw [two_nsmul, two_zsmul]
  -- identify the fold output
  have hfold : (Circuit.foldlRange 255 acc0 (jointLadderBody tables rb sb)
        (jointLadderBody_constantLength tables rb sb)).output n
      = Fin.foldl 255 (fun acc (i : Fin 255) =>
          (jointLadderBody tables rb sb acc ⟨i.val, by omega⟩).output (n + i.val * 12)) acc0 := by
    rw [Circuit.foldlRange.output_eq]
    simp only [hcl]
  have hP := fin_foldl_inv' (fun acc (i : Fin 255) =>
      (jointLadderBody tables rb sb acc i).output (n + i.val * 12)) acc0
    (fun k acc => ladInv Hpt Qpt Rpt env rb sb k acc) hinit hstep 255 (by omega)
  -- put the invariant in terms of the `foldlRange` output, so that the final
  -- `elmTo` step never has to unfold the 255-step `Fin.foldl`
  rw [← hfold] at hP
  -- the final step
  have hc2' : ConstraintsHold.Soundness env
      ((jointLadderFinal tables rb sb
        ((Circuit.foldlRange 255 acc0 (jointLadderBody tables rb sb)
          (jointLadderBody_constantLength tables rb sb)).output n) target).operations
        (n + 3060)) := hc2
  rw [jointLadderFinal_ops] at hc2'
  simp only [ConstraintsHold.Soundness] at hc2'
  rw [Operations.forAllNoOffset_append] at hc2'
  obtain ⟨hm, he⟩ := hc2'
  obtain ⟨hTm, hTval⟩ := mux4W_Tpt env Hpt Qpt Rpt tables rb sb 255 (by norm_num) (n + 3060)
    hb hb' htab hm
  obtain ⟨hns255, hval255⟩ := hP
  have hres := elmTo_sound env _ _ target (n + 3060 + 6) hns255 hTm hT he
  rw [hTval, hval255] at hres
  refine ⟨hT, ?_⟩
  refine hres.symm.trans ?_
  rw [← ladAcc_256 Hpt Qpt Rpt env rb sb hb hb']
  rfl

end StandardECDSA.Phases
