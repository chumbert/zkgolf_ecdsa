/-
# Concrete safe-offset existence (task T14)

The alternating-offset design needs a nonzero offset `H` that avoids every bad
equation of the implementation's family.  This module supplies the *concrete*
candidate set and the counting argument:

* `offsetCandidate k = [k+1]G` for `k : Fin 1040` — 1,040 distinct finite
  points of the P-256 group;
* `offsetCandidate_injective` — the candidates are pairwise distinct, using
  `addOrderOf Gpt = n` and `1040 < n`;
* `exists_goodOffset` — a family of `m < 1040` injective bad equations cannot
  exhaust the candidates, so some candidate avoids all of them;
* `exists_goodOffset_nat` / `findGoodOffset` — the same statement as a bounded
  search over `k < 1040`, with the search result's specification.

Nothing here assumes that `H = G` or `H = [2]G` works: the theorem quantifies
over all 1,040 candidates and only uses `m < 1040`.

The *instantiation* of `BadFamily` with the implementation's 1,039 slots is
task T13 (`Math/OffsetConditions.lean` defines the family type and the generic
counting theorem; the enumeration of the slots is indexed by the actual affine
operations of the phases).
-/

import StandardECDSA.Math.OffsetConditions

namespace StandardECDSA.Math

open StandardECDSA

set_option maxRecDepth 100000

/-! ## The candidate set -/

/-- The `k`-th offset candidate `[k+1]G`, for `k : Fin 1040`. -/
noncomputable def offsetCandidate (k : Fin 1040) : (params.toMathlib).toProjective.Point :=
  (k.val + 1) • Gpt

/-- `1040 < n`, so the candidate indices are all below the group order. -/
theorem thousand_forty_lt_n : 1040 < n := by
  unfold n
  norm_num

/-- The 1,040 candidates are pairwise distinct. -/
theorem offsetCandidate_injective : Function.Injective offsetCandidate := by
  have hn := thousand_forty_lt_n
  intro a b hab
  simp only [offsetCandidate] at hab
  have key : ∀ p q : Nat, p ≤ q → q < 1040 → (p + 1) • Gpt = (q + 1) • Gpt → p = q := by
    intro p q hpq hq heq
    have hd : (q - p) • Gpt = 0 := by
      have h1 : q + 1 = (p + 1) + (q - p) := by omega
      have h2 : (p + 1) • Gpt + (q - p) • Gpt = (p + 1) • Gpt + 0 := by
        rw [add_zero, ← add_nsmul, ← h1]
        exact heq.symm
      exact add_left_cancel h2
    have hdvd : addOrderOf Gpt ∣ (q - p) := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hd
    rw [addOrderOf_Gpt] at hdvd
    rcases Nat.eq_zero_or_pos (q - p) with h0 | hpos
    · omega
    · have hle : n ≤ q - p := Nat.le_of_dvd hpos hdvd
      omega
  rcases le_total a.val b.val with hle | hle
  · have := key a.val b.val hle b.isLt hab
    exact Fin.ext (by omega)
  · have := key b.val a.val hle a.isLt hab.symm
    exact Fin.ext (by omega)

/-! ## Existence -/

/-- **Concrete safe-offset existence.**  A family of `m < 1040` injective bad
equations cannot exhaust the 1,040 candidates `[k+1]G`, so some candidate avoids
every equation of the family. -/
theorem exists_goodOffset (fam : BadFamily (params.toMathlib).toProjective.Point)
    (hm : fam.m < 1040) :
    ∃ k : Fin 1040, fam.Avoids (offsetCandidate k) :=
  exists_avoiding_of_injective fam offsetCandidate offsetCandidate_injective
    (by simpa using hm)

/-- The same statement as a bounded search over `k < 1040`. -/
theorem exists_goodOffset_nat (fam : BadFamily (params.toMathlib).toProjective.Point)
    (hm : fam.m < 1040) :
    ∃ k : Nat, k < 1040 ∧ fam.Avoids ((k + 1) • Gpt) := by
  obtain ⟨k, hk⟩ := exists_goodOffset fam hm
  exact ⟨k.val, k.isLt, hk⟩

/-- The bounded search: a candidate index that avoids the family. -/
noncomputable def findGoodOffset (fam : BadFamily (params.toMathlib).toProjective.Point)
    (hm : fam.m < 1040) : Fin 1040 :=
  Classical.choose (exists_goodOffset fam hm)

/-- The search result avoids every bad equation. -/
theorem findGoodOffset_spec (fam : BadFamily (params.toMathlib).toProjective.Point)
    (hm : fam.m < 1040) :
    fam.Avoids (offsetCandidate (findGoodOffset fam hm)) :=
  Classical.choose_spec (exists_goodOffset fam hm)

/-- The search result is one of the 1,040 candidates. -/
theorem findGoodOffset_lt (fam : BadFamily (params.toMathlib).toProjective.Point)
    (hm : fam.m < 1040) : (findGoodOffset fam hm).val < 1040 :=
  (findGoodOffset fam hm).isLt

/-- The search result is a nonzero multiple of the generator, hence finite. -/
theorem findGoodOffset_ne_zero (fam : BadFamily (params.toMathlib).toProjective.Point)
    (hm : fam.m < 1040) : offsetCandidate (findGoodOffset fam hm) ≠ 0 := by
  have hn := thousand_forty_lt_n
  intro h
  have hk := findGoodOffset_lt fam hm
  have hpos : 0 < (findGoodOffset fam hm).val + 1 := Nat.succ_pos _
  have hzero : ((findGoodOffset fam hm).val + 1) • Gpt = 0 := h
  have hdvd : addOrderOf Gpt ∣ ((findGoodOffset fam hm).val + 1) :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr hzero
  rw [addOrderOf_Gpt] at hdvd
  have := Nat.le_of_dvd hpos hdvd
  omega

end StandardECDSA.Math
