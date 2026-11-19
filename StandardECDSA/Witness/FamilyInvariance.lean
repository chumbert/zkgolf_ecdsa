/-
# The bad-equation family depends only on the bit wires

`famOf env eb rb sb Qpt Rpt` (`Math/OffsetFamily.lean`) is the concrete family of
1,293 bad equations of the standard circuit.  Its targets are built from `G`, `Q`,
`R` and the fixed shift `S`, and read the environment only through the *bit*
wires `eb`, `rb`, `sb` (`digitOf`, `winSum`, `rBitAt`, `tBitAt`, `bitSum`,
`bitSumT`).

That is what makes the honest-witness construction well defined: the seed's
offset `H` is chosen to avoid `famOf env …`, while `env` itself is built from the
seed.  The circularity is broken by this module's congruence lemma — two
environments that agree on the bit wires generate the *same* family, and the bit
wires are determined by the seed's `rBits`/`tBits`/`digestBits`, which do not
depend on the offset.

No new axioms, no `native_decide`, no `sorry`.
-/
import StandardECDSA.Math.OffsetFamily
import StandardECDSA.Phases.LadderSemantics
import StandardECDSA.Phases.FixedBaseSemantics

namespace StandardECDSA

open Circuit
open StandardECDSA.Gadgets
open StandardECDSA.Math
open StandardECDSA.Phases
open WeierstrassCurve

/-! ## The bit reads -/

/-- `digitOf` depends only on the `eb` wires. -/
theorem digitOf_congr (env1 env2 : Environment Fp) (eb : Vector E 256)
    (h : ∀ k : Fin 256, Expression.eval env1 (eb.get k) = Expression.eval env2 (eb.get k))
    (i : Nat) : digitOf env1 eb i = digitOf env2 eb i := by
  unfold digitOf
  rw [h ⟨2 * i % 256, Nat.mod_lt _ (by norm_num)⟩,
    h ⟨(2 * i + 1) % 256, Nat.mod_lt _ (by norm_num)⟩]

/-- `winSum` depends only on the `eb` wires. -/
theorem winSum_congr (env1 env2 : Environment Fp) (eb : Vector E 256)
    (h : ∀ k : Fin 256, Expression.eval env1 (eb.get k) = Expression.eval env2 (eb.get k))
    (k : Nat) : winSum env1 eb k = winSum env2 eb k := by
  unfold winSum
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [digitOf_congr env1 env2 eb h i]

/-- `rBitAt` depends only on the `rb` wires. -/
theorem rBitAt_congr (env1 env2 : Environment Fp) (rb : Vector E 256)
    (h : ∀ k : Fin 256, Expression.eval env1 (rb.get k) = Expression.eval env2 (rb.get k))
    (j : Nat) : rBitAt env1 rb j = rBitAt env2 rb j := by
  unfold rBitAt
  rw [h ⟨255 - j, by omega⟩]

/-- `tBitAt` depends only on the `sb` wires. -/
theorem tBitAt_congr (env1 env2 : Environment Fp) (sb : Vector E 256)
    (h : ∀ k : Fin 256, Expression.eval env1 (sb.get k) = Expression.eval env2 (sb.get k))
    (j : Nat) : tBitAt env1 sb j = tBitAt env2 sb j := by
  unfold tBitAt
  rw [h ⟨255 - j, by omega⟩]

/-- `bitSum` depends only on the `rb` wires. -/
theorem bitSum_congr (env1 env2 : Environment Fp) (rb : Vector E 256)
    (h : ∀ k : Fin 256, Expression.eval env1 (rb.get k) = Expression.eval env2 (rb.get k))
    (j : Nat) : bitSum env1 rb j = bitSum env2 rb j := by
  unfold bitSum
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [rBitAt_congr env1 env2 rb h i]

/-- `bitSumT` depends only on the `sb` wires. -/
theorem bitSumT_congr (env1 env2 : Environment Fp) (sb : Vector E 256)
    (h : ∀ k : Fin 256, Expression.eval env1 (sb.get k) = Expression.eval env2 (sb.get k))
    (j : Nat) : bitSumT env1 sb j = bitSumT env2 sb j := by
  unfold bitSumT
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [tBitAt_congr env1 env2 sb h i]

/-- `ladOff` depends only on the bit wires. -/
theorem ladOff_congr (env1 env2 : Environment Fp) (Qpt Rpt : Affine.Point Wp)
    (rb sb : Vector E 256)
    (hrb : ∀ k : Fin 256, Expression.eval env1 (rb.get k) = Expression.eval env2 (rb.get k))
    (hsb : ∀ k : Fin 256, Expression.eval env1 (sb.get k) = Expression.eval env2 (sb.get k))
    (j : Nat) : ladOff env1 Qpt Rpt rb sb j = ladOff env2 Qpt Rpt rb sb j := by
  unfold ladOff
  rw [bitSum_congr env1 env2 rb hrb j, bitSumT_congr env1 env2 sb hsb j]

/-! ## The targets -/

/-- Every target of the family depends only on the bit wires. -/
theorem targetOf_congr (env1 env2 : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp)
    (heb : ∀ k : Fin 256, Expression.eval env1 (eb.get k) = Expression.eval env2 (eb.get k))
    (hrb : ∀ k : Fin 256, Expression.eval env1 (rb.get k) = Expression.eval env2 (rb.get k))
    (hsb : ∀ k : Fin 256, Expression.eval env1 (sb.get k) = Expression.eval env2 (sb.get k))
    (s : SlotIx) : targetOf env1 eb rb sb Qpt Rpt s = targetOf env2 eb rb sb Qpt Rpt s := by
  rcases s with b | ⟨i, b⟩ | u | ⟨k, b⟩ | ⟨j, b⟩ | ⟨j, b⟩
  · cases b <;> rfl
  · cases b <;>
      simp only [targetOf, digitOf_congr env1 env2 eb heb i.val,
        winSum_congr env1 env2 eb heb i.val]
  · rfl
  · cases b <;> rfl
  · cases b <;>
      simp only [targetOf, ladOff_congr env1 env2 Qpt Rpt rb sb hrb hsb j.val,
        rBitAt_congr env1 env2 rb hrb j.val, tBitAt_congr env1 env2 sb hsb j.val]
  · cases b <;>
      simp only [targetOf, ladOff_congr env1 env2 Qpt Rpt rb sb hrb hsb j.val,
        rBitAt_congr env1 env2 rb hrb j.val, tBitAt_congr env1 env2 sb hsb j.val]

/-! ## The family -/

/-- **The bad-equation family depends only on the bit wires.** -/
theorem famOf_congr (env1 env2 : Environment Fp) (eb rb sb : Vector E 256)
    (Qpt Rpt : Affine.Point Wp)
    (heb : ∀ k : Fin 256, Expression.eval env1 (eb.get k) = Expression.eval env2 (eb.get k))
    (hrb : ∀ k : Fin 256, Expression.eval env1 (rb.get k) = Expression.eval env2 (rb.get k))
    (hsb : ∀ k : Fin 256, Expression.eval env1 (sb.get k) = Expression.eval env2 (sb.get k)) :
    famOf env1 eb rb sb Qpt Rpt = famOf env2 eb rb sb Qpt Rpt := by
  have h : ∀ i : Fin 1293, (famOf env1 eb rb sb Qpt Rpt).target i
      = (famOf env2 eb rb sb Qpt Rpt).target i := by
    intro i
    show targetOf env1 eb rb sb Qpt Rpt (slotEquiv.symm i)
      = targetOf env2 eb rb sb Qpt Rpt (slotEquiv.symm i)
    exact targetOf_congr env1 env2 eb rb sb Qpt Rpt heb hrb hsb _
  unfold famOf
  congr 1
  funext i
  exact h i

end StandardECDSA
