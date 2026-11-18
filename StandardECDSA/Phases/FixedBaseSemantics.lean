/-
# Fixed-base phase: group semantics (`ep = H + [E]G`)

Plan §5 fixed-base prefix invariant:

```text
ep_k = H - S + Σ_{i<k} [(4 + d_i)·4^i]G,      ep_128 = H + [E]G
```

with `d_i = eBit[2i] + 2·eBit[2i+1]` and `S = [4·(4^128 - 1)/3]G`.

This module proves the group-level half of task T12: the kernel-certified table
entries of `Math/FixedTables.lean` are the points `[(4+d)·4^i]G`, the constant
mux selects the entry indexed by `b0 + 2·b1`, and the 128-step fold carries the
prefix invariant.  The row-level halves are in `Phases/TableSemantics.lean` and
`Phases/Semantics.lean`.

Task T12 (fixed-base half).
-/

import StandardECDSA.Phases.TableSemantics
import StandardECDSA.Phases.Semantics
import StandardECDSA.Math.FixedTables
import StandardECDSA.Math.ScalarEncoding

namespace StandardECDSA.Phases

open StandardECDSA
open StandardECDSA.Gadgets
open StandardECDSA.Math
open StandardECDSA.Math.FixedTables
open WeierstrassCurve
open scoped BigOperators

/-! ## The generator point in the affine group -/

theorem n_pos : 0 < n := by have := n_prime.two_le; omega

/-- `mulG k` is finite whenever `k % n ≠ 0`. -/
theorem mulG_mod_self (k : Nat) : mulG k = mulG (k % n) := by
  simp only [mulG, Nat.mod_mod_of_dvd _ (dvd_refl n)]

theorem mulG_Z_ne_zero_gen (k : Nat) (hk : k % n ≠ 0) : (mulG k).Z ≠ 0 := by
  rw [mulG_mod_self]
  exact mulG_Z_ne_zero (Nat.pos_of_ne_zero hk) (Nat.mod_lt _ n_pos)

/-- `mulG k` is the affine group element `k • G`, for any `k` with `k % n ≠ 0`. -/
theorem mulG_affine_some_gen (k : Nat) (hk : k % n ≠ 0) :
    Affine.Point.some (affine (mulG k)).1 (affine (mulG k)).2
        (affine_ns (mulG k) (mulG_on_curve k) (mulG_Z_ne_zero_gen k hk))
      = WeierstrassCurve.Projective.Point.toAffineLift (k • Gpt) := by
  rw [← toAffinePt_eq_some]
  exact (toAffinePt_eq_toAffineLift (mulG k) (mulG_on_curve k)
    (mulG_Z_ne_zero_gen k hk)).trans
    (congrArg WeierstrassCurve.Projective.Point.toAffineLift (mulG_toMathlib k))

/-! ## Table entries as group points -/

/-- The group point of the table entry `(i, d)`: `[(4+d)·4^i]G`. -/
noncomputable def tablePt (i d : Nat) : Affine.Point Wp :=
  WeierstrassCurve.Projective.Point.toAffineLift (((4 + d) * 4 ^ i) • Gpt)

/-- `(4+d)·4^i` is not divisible by `n` for `d < 4` and `i < 128`. -/
theorem tableNat_mod_ne_zero (i d : Nat) (hd : d < 4) (hi : i < 128) :
    ((4 + d) * 4 ^ i) % n ≠ 0 := by
  intro h0
  have hdvd : n ∣ (4 + d) * 4 ^ i := Nat.dvd_of_mod_eq_zero h0
  have hn7 : 7 < n := by decide
  rcases n_prime.dvd_mul.mp hdvd with h | h
  · have := Nat.le_of_dvd (by omega) h
    omega
  · have h4 : n ∣ 4 := n_prime.dvd_of_dvd_pow (m := 4) h
    have h2 : n ∣ 2 := n_prime.dvd_of_dvd_pow (m := 2) (n := 2) (show n ∣ 2 ^ 2 from h4)
    have := Nat.le_of_dvd (by norm_num) h2
    omega

/-- The kernel-certified table entry is the group point `[(4+d)·4^i]G`. -/
theorem tableEntry_some (i d : Nat) (hd : d < 4) (hi : i < 128) :
    Affine.Point.some (tableEntry i d).1 (tableEntry i d).2
        (affine_ns (mulG ((4 + d) * 4 ^ i)) (mulG_on_curve ((4 + d) * 4 ^ i))
          (mulG_Z_ne_zero_gen _ (tableNat_mod_ne_zero i d hd hi)))
      = tablePt i d :=
  mulG_affine_some_gen ((4 + d) * 4 ^ i) (tableNat_mod_ne_zero i d hd hi)

/-- The fixed-base shift `S = [4·(4^128 - 1)/3]G` as a group point. -/
noncomputable def shiftPt : Affine.Point Wp :=
  WeierstrassCurve.Projective.Point.toAffineLift (shiftNat • Gpt)

theorem shiftNat_mod_ne_zero : shiftNat % n ≠ 0 := by decide

theorem fixedShift_some :
    Affine.Point.some fixedShift.1 fixedShift.2
        (affine_ns (mulG shiftNat) (mulG_on_curve shiftNat)
          (mulG_Z_ne_zero_gen shiftNat shiftNat_mod_ne_zero))
      = shiftPt :=
  mulG_affine_some_gen shiftNat shiftNat_mod_ne_zero

/-! ## The constant mux selects the certified table entry -/

/-- The fixed table row `i`, as an `Array` with a size proof. -/
def fbTab (i : Nat) (hi : i < 128) : Array (Fp × Fp) :=
  fixedTables[i]'(by rw [fixedTables_size]; exact hi)

theorem fixedTables_getD (i j : Nat) (hi : i < fixedTables.size) (hj : j < 4) :
    (fixedTables[i]'hi).getD j (0, 0) = tableEntry i j := by
  have hs : j < (fixedTables[i]'hi).size := by rw [fixedTables_row_size i hi]; exact hj
  simp only [Array.getD, dif_pos hs]
  exact fixedTables_get i j hi hs

/-- The two output coordinates of `muxConst4W` on the fixed table row `i` are the
coordinates of the entry indexed by `b0 + 2·b1`. -/
theorem muxConst4W_coords (env : Environment Fp) (i : Nat) (hi : i < 128)
    (b0 b1 : E) (n : Nat)
    (hb0 : Expression.eval env b0 = 0 ∨ Expression.eval env b0 = 1)
    (hb1 : Expression.eval env b1 = 0 ∨ Expression.eval env b1 = 1)
    (hrow : Expression.eval env (pm b0 b1 - Expression.var (F := Fp) ⟨n⟩) = 0) :
    Expression.eval env ((Circuit.output (muxConst4W b0 b1 (fbTab i hi)) n).1)
        = (tableEntry i ((Expression.eval env b0).val
            + 2 * (Expression.eval env b1).val)).1
      ∧ Expression.eval env ((Circuit.output (muxConst4W b0 b1 (fbTab i hi)) n).2)
        = (tableEntry i ((Expression.eval env b0).val
            + 2 * (Expression.eval env b1).val)).2 := by
  obtain ⟨e1, e2⟩ := muxConst4W_eval env b0 b1 (fbTab i hi) n hrow
  have h0 : (fbTab i hi).getD 0 (0, 0) = tableEntry i 0 :=
    fixedTables_getD i 0 _ (by norm_num)
  have h1 : (fbTab i hi).getD 1 (0, 0) = tableEntry i 1 :=
    fixedTables_getD i 1 _ (by norm_num)
  have h2 : (fbTab i hi).getD 2 (0, 0) = tableEntry i 2 :=
    fixedTables_getD i 2 _ (by norm_num)
  have h3 : (fbTab i hi).getD 3 (0, 0) = tableEntry i 3 :=
    fixedTables_getD i 3 _ (by norm_num)
  rw [h0, h1, h2, h3] at e1 e2
  rw [muxConst4Val_bits _ _ _ _ _ _ hb0 hb1] at e1 e2
  rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;>
    simp only [hb0, hb1, ZMod.val_zero, ZMod.val_one, Nat.zero_add, Nat.reduceAdd,
      if_true, if_false] at e1 e2 ⊢ <;> exact ⟨e1, e2⟩

/-- The constant mux output is the group point `[(4 + b0 + 2·b1)·4^i]G`. -/
theorem muxConst4W_tablePt (env : Environment Fp) (i : Nat) (hi : i < 128)
    (b0 b1 : E) (n : Nat)
    (hb0 : Expression.eval env b0 = 0 ∨ Expression.eval env b0 = 1)
    (hb1 : Expression.eval env b1 = 0 ∨ Expression.eval env b1 = 1)
    (hrow : Expression.eval env (pm b0 b1 - Expression.var (F := Fp) ⟨n⟩) = 0) :
    ∃ hns : NS (Expression.eval env ((Circuit.output (muxConst4W b0 b1 (fbTab i hi)) n).1))
        (Expression.eval env ((Circuit.output (muxConst4W b0 b1 (fbTab i hi)) n).2)),
      Affine.Point.some _ _ hns
        = tablePt i ((Expression.eval env b0).val + 2 * (Expression.eval env b1).val) := by
  obtain ⟨e1, e2⟩ := muxConst4W_coords env i hi b0 b1 n hb0 hb1 hrow
  have hd : (Expression.eval env b0).val + 2 * (Expression.eval env b1).val < 4 := by
    rcases hb0 with h | h <;> rcases hb1 with h' | h' <;>
      simp only [h, h', ZMod.val_zero, ZMod.val_one] <;> omega
  refine ⟨ns_congr e1 e2 (affine_ns (mulG ((4 + _) * 4 ^ i)) (mulG_on_curve _)
    (mulG_Z_ne_zero_gen _ (tableNat_mod_ne_zero i _ hd hi))), ?_⟩
  exact (some_congr e1 e2 _ _).trans (tableEntry_some i _ hd hi)

end StandardECDSA.Phases
