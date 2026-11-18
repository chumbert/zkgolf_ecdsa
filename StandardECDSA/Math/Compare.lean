/-
# Comparison mathematics for the constant-bound comparator

`Gadgets/Scalar.lean` implements `assertLtOrderOf bound a` (assert `a ≤ bound`)
and its guarded variant `assertLtOrderGuardedOf bound guard a` (assert
`guard = 1 → a ≤ bound`) by scanning the maximal runs of equal bits of `bound`,
most significant first.  For every maximal ZERO run `[lo, hi]` it emits one row

```text
missing * quotient = sum
```

where `sum` is the sum of the bits of `a` on the run and `missing` counts the
missing ONE bits of `bound` above the run.

This module supplies the pure arithmetic behind those rows:

* `prefVal`/`boundNat`/`RunsCover` and the kernel-checked run decompositions of
  `n - 1` and `(p - n) - 1`;
* `prefVal_le_of_runs`: if every zero run of `bound` is forced to zero whenever
  the ONE bits above it are matched, then the bits spell at most `bound`;
* `missAbove`/`runSumVal` and the split identities used by the loop invariant;
* the "no wraparound" lemma: a sum of at most 256 Boolean bits vanishes in the
  field only if it vanishes as a natural.

Task T06.
-/

import StandardECDSA.Gadgets.Scalar

namespace StandardECDSA.Gadgets

open StandardECDSA.Math
open Challenge.Instances.ECDSA_P256_Digest.Interface

set_option maxRecDepth 100000

/-! ## Bits and prefix values, most significant first -/

/-- Bit `j` (most significant first) of `bound`, as a `Bool`. -/
def bBit (bound j : Nat) : Bool := bitAt bound (255 - j)

/-- Bit `j` (most significant first) of `bound`, as a natural. -/
def boundNat (bound j : Nat) : Nat := if bBit bound j then 1 else 0

/-- Value of the first `k` entries of `x`, most significant first. -/
def prefVal (x : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => 2 * prefVal x k + x k

theorem prefVal_congr {x y : Nat → Nat} {k : Nat} (h : ∀ j < k, x j = y j) :
    prefVal x k = prefVal y k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [prefVal, ih (fun j hj => h j (by omega)), h k (by omega)]

/-! ## The run decomposition of a bound -/

/-- Boolean form of "`l` is the list of maximal runs of `bound` covering exactly
the positions below `p`, most significant first".  Written as a `Bool` so that
`decide` can certify the two concrete bounds. -/
def RunsCoverB (bound : Nat) : Nat → List (Nat × Nat × Bool) → Bool
  | p, [] => p == 0
  | p, r :: rest =>
      (r.1 + 1 == p) && (r.2.1 ≤ r.1) &&
      ((List.range (r.1 + 1 - r.2.1)).all (fun j => bitAt bound (r.2.1 + j) == r.2.2)) &&
      RunsCoverB bound r.2.1 rest

/-- `l` is the list of maximal runs of `bound` covering exactly the positions
below `p`, most significant first. -/
abbrev RunsCover (bound p : Nat) (l : List (Nat × Nat × Bool)) : Prop :=
  RunsCoverB bound p l = true

theorem runsCover_n : RunsCover nSubOne 256 (boundRunsOf nSubOne) := by
  decide +kernel

theorem runsCover_pn : RunsCover pSubNSubOne 256 (boundRunsOf pSubNSubOne) := by
  decide +kernel

theorem prefVal_boundNat_n : prefVal (boundNat nSubOne) 256 = nSubOne := by
  decide +kernel

theorem prefVal_boundNat_pn : prefVal (boundNat pSubNSubOne) 256 = pSubNSubOne := by
  decide +kernel

/-! ## Consequences of `RunsCover` -/

theorem RunsCover.le {bound p : Nat} {l : List (Nat × Nat × Bool)}
    (h : RunsCover bound p l) : ∀ r ∈ l, r.2.1 ≤ r.1 := by
  induction l generalizing p with
  | nil => intro r hr; simp at hr
  | cons s rest ih =>
      intro r' hr'
      simp only [RunsCover, RunsCoverB, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at h
      obtain ⟨⟨⟨-, hle⟩, -⟩, hrest⟩ := h
      rcases List.mem_cons.mp hr' with rfl | hr'
      · exact hle
      · exact ih hrest r' hr'

theorem RunsCover.bits {bound p : Nat} {l : List (Nat × Nat × Bool)}
    (h : RunsCover bound p l) :
    ∀ r ∈ l, ∀ k, r.2.1 ≤ k → k ≤ r.1 → bitAt bound k = r.2.2 := by
  induction l generalizing p with
  | nil => intro r hr; simp at hr
  | cons s rest ih =>
      intro r' hr'
      simp only [RunsCover, RunsCoverB, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at h
      obtain ⟨⟨⟨-, -⟩, hbits⟩, hrest⟩ := h
      rcases List.mem_cons.mp hr' with rfl | hr'
      · intro k h1 h2
        have hmem : k - r'.2.1 ∈ List.range (r'.1 + 1 - r'.2.1) :=
          List.mem_range.mpr (by omega)
        have hthis := List.all_eq_true.mp hbits (k - r'.2.1) hmem
        simp only [beq_iff_eq] at hthis
        have hk : r'.2.1 + (k - r'.2.1) = k := Nat.add_sub_cancel' h1
        rw [hk] at hthis
        exact hthis
      · exact ih hrest r' hr'

/-- Every run of a cover of `[0, p)` lies below `p`. -/
theorem RunsCover.hi_lt {bound p : Nat} {l : List (Nat × Nat × Bool)}
    (h : RunsCover bound p l) : ∀ r ∈ l, r.1 < p := by
  induction l generalizing p with
  | nil => intro r hr; simp at hr
  | cons s rest ih =>
      intro r' hr'
      simp only [RunsCover, RunsCoverB, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at h
      obtain ⟨⟨⟨hhead, hle⟩, -⟩, hrest⟩ := h
      rcases List.mem_cons.mp hr' with rfl | hr'
      · omega
      · have := ih hrest r' hr'
        omega

/-- Every position below `p` lies in one of the runs. -/
theorem RunsCover.cover {bound p : Nat} {l : List (Nat × Nat × Bool)}
    (h : RunsCover bound p l) : ∀ j, j < p → ∃ r ∈ l, r.2.1 ≤ j ∧ j ≤ r.1 := by
  induction l generalizing p with
  | nil =>
      intro j hj
      simp only [RunsCover, RunsCoverB, beq_iff_eq] at h
      omega
  | cons s rest ih =>
      intro j hj
      simp only [RunsCover, RunsCoverB, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at h
      obtain ⟨⟨⟨hhead, hle⟩, -⟩, hrest⟩ := h
      by_cases hlo : s.2.1 ≤ j
      · exact ⟨s, List.mem_cons_self .., hlo, by omega⟩
      · obtain ⟨r', hr', h1, h2⟩ := ih hrest j (by omega)
        exact ⟨r', List.mem_cons_of_mem _ hr', h1, h2⟩

/-! ## The comparison core -/

/-- The core comparison: bits satisfying every zero-run implication spell at most
`bound`. -/
theorem prefVal_le_of_runs (bound : Nat) (x : Nat → Nat) (hx : ∀ j < 256, x j ≤ 1)
    (hpref : prefVal (boundNat bound) 256 = bound)
    (hcover : RunsCover bound 256 (boundRunsOf bound))
    (hruns : ∀ r ∈ boundRunsOf bound, r.2.2 = false →
      (∀ j < 255 - r.1, bBit bound j = true → x j = 1) →
      ∀ j, 255 - r.1 ≤ j → j ≤ 255 - r.2.1 → x j = 0) :
    prefVal x 256 ≤ bound := by
  have key : ∀ k ≤ 256, prefVal x k < prefVal (boundNat bound) k ∨
      ∀ j < k, x j = boundNat bound j := by
    intro k _
    induction k with
    | zero => exact Or.inr (fun j hj => absurd hj (Nat.not_lt_zero j))
    | succ k ih =>
        rcases ih (by omega) with hlt | heq
        · left
          have := hx k (by omega)
          simp only [prefVal]
          omega
        · have hval := prefVal_congr heq
          cases hb : bBit bound k with
          | true =>
              rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hx k (by omega)) with h0 | h1
              · left
                simp only [prefVal, hval, h0, boundNat, hb, ↓reduceIte]
                omega
              · right
                intro j hj
                rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
                · exact heq j hj
                · simp [boundNat, hb, h1]
          | false =>
              obtain ⟨r, hr, hlo, hhi⟩ := RunsCover.cover hcover (255 - k) (by omega)
              have hpre : ∀ j < 255 - r.1, bBit bound j = true → x j = 1 := by
                intro j hj hbj
                have hjk : j < k := by omega
                rw [heq j hjk]
                simp only [boundNat, hbj, ↓reduceIte]
              have hrf : r.2.2 = false := by
                have hb' := RunsCover.bits hcover r hr (255 - k) (by omega) (by omega)
                rw [show 255 - k = 255 - k from rfl] at hb'
                rw [← hb']
                exact hb
              have hk0 := hruns r hr hrf hpre k (by omega) (by omega)
              right
              intro j hj
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
              · exact heq j hj
              · simp only [boundNat, hb, hk0, Bool.false_eq_true, ↓reduceIte]
  rw [← hpref]
  rcases key 256 le_rfl with hlt | heq
  · exact hlt.le
  · exact (prefVal_congr heq).le

/-! ## The missing-bit count and the run sum -/

/-- `1 - av k` on the ONE bits of `bound`, `0` elsewhere. -/
def missTerm (av : Nat → Fp) (bound k : Nat) : Fp :=
  if bitAt bound k then 1 - av k else 0

/-- The missing ONE bits of `bound` at positions `≥ p`. -/
def missAbove (av : Nat → Fp) (bound p : Nat) : Fp :=
  ∑ k ∈ Finset.range (256 - p), missTerm av bound (p + k)

/-- The missing ONE bits of `bound` on the run `[lo, hi]`. -/
def missRunVal (av : Nat → Fp) (bound hi lo : Nat) : Fp :=
  ∑ k ∈ Finset.range (hi + 1 - lo), missTerm av bound (lo + k)

/-- The sum of the bits of `a` on the run `[lo, hi]`. -/
def runSumVal (av : Nat → Fp) (hi lo : Nat) : Fp :=
  ∑ j ∈ Finset.range (hi - lo + 1), av (hi - j)

theorem missAbove_split (av : Nat → Fp) (bound lo p : Nat) (h : lo ≤ p) (hp : p ≤ 256)
    (hp1 : 1 ≤ p) :
    missAbove av bound lo =
      missRunVal av bound (p - 1) lo + missAbove av bound p := by
  unfold missAbove missRunVal
  have h256 : 256 - lo = (p - lo) + (256 - p) := by omega
  have hpl : p - 1 + 1 - lo = p - lo := by omega
  rw [h256, Finset.sum_range_add, hpl]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  omega

/-- A foldl of a range is the initial value plus the sum. -/
theorem foldl_range_add {M : Type*} [AddCommMonoid M] (g : Nat → M) (init : M) (n : Nat) :
    (List.range n).foldl (fun m j => m + g j) init = init + ∑ j ∈ Finset.range n, g j := by
  induction n generalizing init with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
        Finset.sum_range_succ, add_assoc]

/-- Evaluating a foldl of a range. -/
theorem eval_foldl_range (env : Environment Fp) (f : E → Nat → E) (g : Nat → Fp) (init : E)
    (n : Nat) (hf : ∀ acc j, Expression.eval env (f acc j) = Expression.eval env acc + g j) :
    Expression.eval env ((List.range n).foldl f init) =
      Expression.eval env init + ∑ j ∈ Finset.range n, g j := by
  induction n generalizing init with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hf, ih,
        Finset.sum_range_succ, add_assoc]

theorem eval_addMissing (env : Environment Fp) (av : Nat → Fp) (a : Nat → E)
    (ha : ∀ k, Expression.eval env (a k) = av k) (hi lo : Nat) (m : E) :
    Expression.eval env (addMissing a hi lo m) =
      Expression.eval env m + ∑ j ∈ Finset.range (hi - lo + 1), (1 - av (hi - j)) := by
  unfold addMissing
  rw [eval_foldl_range env _ (fun j => 1 - av (hi - j)) m _ (fun acc j => by
    simp only [circuit_norm, cst, ha])]

theorem eval_runSum (env : Environment Fp) (av : Nat → Fp) (a : Nat → E)
    (ha : ∀ k, Expression.eval env (a k) = av k) (hi lo : Nat) :
    Expression.eval env (runSum a hi lo) = runSumVal av hi lo := by
  unfold runSum runSumVal
  rw [eval_foldl_range env _ (fun j => av (hi - j)) (cst 0) _ (fun acc j => by
    simp only [circuit_norm, cst, ha])]
  simp only [circuit_norm, cst]

/-! ## Boolean bits as naturals -/

/-- The natural value of the field element `av k`, assuming it is Boolean. -/
def aNatOf (av : Nat → Fp) (k : Nat) : Nat := if av k = 1 then 1 else 0

theorem aNatOf_le_one (av : Nat → Fp) (k : Nat) : aNatOf av k ≤ 1 := by
  unfold aNatOf; split <;> omega

theorem aNatOf_cast {av : Nat → Fp} {k : Nat} (h : av k = 0 ∨ av k = 1) :
    av k = (aNatOf av k : Fp) := by
  rcases h with h0 | h1
  · rw [h0]; simp [aNatOf, h0]
  · rw [h1]; simp [aNatOf, h1]

/-- A sum of at most 256 Boolean bits vanishes in the field only if it vanishes
as a natural. -/
theorem natSum_eq_zero {n : Nat} (hn : n ≤ 256) (f : Nat → Nat) (hf : ∀ j, f j ≤ 1)
    (h : ((∑ j ∈ Finset.range n, f j : Nat) : Fp) = 0) :
    ∀ j ∈ Finset.range n, f j = 0 := by
  have hle : (∑ j ∈ Finset.range n, f j) ≤ 256 := by
    calc (∑ j ∈ Finset.range n, f j) ≤ ∑ _j ∈ Finset.range n, 1 :=
          Finset.sum_le_sum fun j _ => hf j
      _ = n := by simp
      _ ≤ 256 := hn
  have hprime : (256 : Nat) < circuitPrime := by decide
  have hlt : (∑ j ∈ Finset.range n, f j) < circuitPrime := by omega
  rw [ZMod.natCast_eq_zero_iff] at h
  have h0 := Nat.eq_zero_of_dvd_of_lt h hlt
  intro j hj
  exact (Finset.sum_eq_zero_iff.mp h0) j hj

/-- Reindexing a range sum by reflection. -/
theorem sum_range_reflect' (f : Nat → Fp) (hi lo : Nat) (h : lo ≤ hi) :
    (∑ j ∈ Finset.range (hi - lo + 1), f (hi - j)) =
      ∑ k ∈ Finset.range (hi - lo + 1), f (lo + k) := by
  rw [← Finset.sum_range_reflect (fun i => f (lo + i)) (hi - lo + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  congr 1
  omega

/-- The missing count on a run whose bits are all `b`. -/
theorem missRunVal_of_bits (av : Nat → Fp) (bound hi lo : Nat) (b : Bool)
    (hbits : ∀ k, lo ≤ k → k ≤ hi → bitAt bound k = b) :
    missRunVal av bound hi lo =
      if b then ∑ k ∈ Finset.range (hi + 1 - lo), (1 - av (lo + k)) else 0 := by
  unfold missRunVal
  cases b with
  | true =>
      simp only [if_true]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_range] at hk
      unfold missTerm
      rw [hbits (lo + k) (by omega) (by omega)]
      simp
  | false =>
      simp only [if_false, Bool.false_eq_true]
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_range] at hk
      unfold missTerm
      rw [hbits (lo + k) (by omega) (by omega)]
      simp

/-- The run sum as the cast of a natural sum. -/
theorem runSumVal_cast (av : Nat → Fp) (hi lo : Nat) (h : lo ≤ hi)
    (hb : ∀ k, lo ≤ k → k ≤ hi → av k = 0 ∨ av k = 1) :
    runSumVal av hi lo =
      ((∑ j ∈ Finset.range (hi - lo + 1), aNatOf av (hi - j) : Nat) : Fp) := by
  unfold runSumVal
  push_cast
  exact Finset.sum_congr rfl fun j hj => by
    simp only [Finset.mem_range] at hj
    exact aNatOf_cast (hb (hi - j) (by omega) (by omega))

/-- A vanishing run sum forces every bit of the run to zero. -/
theorem runSumVal_eq_zero (av : Nat → Fp) (hi lo : Nat) (h : lo ≤ hi) (hhi : hi ≤ 255)
    (hb : ∀ k, lo ≤ k → k ≤ hi → av k = 0 ∨ av k = 1) (h0 : runSumVal av hi lo = 0) :
    ∀ k, lo ≤ k → k ≤ hi → av k = 0 := by
  rw [runSumVal_cast av hi lo h hb] at h0
  have hle : hi - lo + 1 ≤ 256 := by omega
  have hz := natSum_eq_zero hle (fun j => aNatOf av (hi - j)) (fun j => aNatOf_le_one av _) h0
  intro k h1 h2
  have hmem : hi - k ∈ Finset.range (hi - lo + 1) := Finset.mem_range.mpr (by omega)
  have hk := hz (hi - k) hmem
  have hkk : hi - (hi - k) = k := by omega
  rw [hkk] at hk
  rcases hb k h1 h2 with h' | h'
  · exact h'
  · simp [aNatOf, h'] at hk

/-! ## Prefix monotonicity (used by completeness) -/

theorem prefVal_add (x : Nat → Nat) (m k : Nat) :
    prefVal x (m + k) = prefVal x m * 2 ^ k + prefVal (fun j => x (m + j)) k := by
  induction k with
  | zero =>
      rw [Nat.add_zero, pow_zero, mul_one]
      show prefVal x m = prefVal x m + prefVal (fun j => x (m + j)) 0
      rw [show prefVal (fun j => x (m + j)) 0 = 0 from rfl, add_zero]
  | succ k ih =>
      rw [Nat.add_succ, prefVal, ih, prefVal, Nat.pow_succ]
      ring

theorem prefVal_lt_two_pow (y : Nat → Nat) (k : Nat) (hy : ∀ j < k, y j ≤ 1) :
    prefVal y k < 2 ^ k := by
  induction k with
  | zero => show (0 : Nat) < 1; exact Nat.zero_lt_one
  | succ k ih =>
      have h1 := ih (fun j hj => hy j (by omega))
      have h2 := hy k (by omega)
      rw [prefVal, Nat.pow_succ]
      omega

/-- A strictly larger prefix value stays strictly larger. -/
theorem prefVal_lt_of_lt {x y : Nat → Nat} {m : Nat} (hm : m ≤ 256)
    (h : prefVal y m < prefVal x m) (hy : ∀ j, m ≤ j → j < 256 → y j ≤ 1) :
    prefVal y 256 < prefVal x 256 := by
  have hd : m ≤ 256 := hm
  have e1 : prefVal y 256 = prefVal y m * 2 ^ (256 - m) +
      prefVal (fun j => y (m + j)) (256 - m) := by
    rw [← prefVal_add, Nat.add_sub_cancel' hd]
  have e2 : prefVal x 256 = prefVal x m * 2 ^ (256 - m) +
      prefVal (fun j => x (m + j)) (256 - m) := by
    rw [← prefVal_add, Nat.add_sub_cancel' hd]
  have hlt : prefVal (fun j => y (m + j)) (256 - m) < 2 ^ (256 - m) :=
    prefVal_lt_two_pow _ _ (fun j hj => hy (m + j) (by omega) (by omega))
  have hge : (prefVal y m + 1) * 2 ^ (256 - m) ≤ prefVal x m * 2 ^ (256 - m) :=
    Nat.mul_le_mul_right _ h
  rw [e1, e2]
  calc prefVal y m * 2 ^ (256 - m) + prefVal (fun j => y (m + j)) (256 - m)
      < prefVal y m * 2 ^ (256 - m) + 2 ^ (256 - m) := Nat.add_lt_add_left hlt _
    _ = (prefVal y m + 1) * 2 ^ (256 - m) := by ring
    _ ≤ prefVal x m * 2 ^ (256 - m) := hge
    _ ≤ prefVal x m * 2 ^ (256 - m) + prefVal (fun j => x (m + j)) (256 - m) :=
        Nat.le_add_right _ _

/-- The missing count as a natural number. -/
def missNat (av : Nat → Fp) (bound p : Nat) : Nat :=
  ∑ k ∈ Finset.range (256 - p),
    (if bitAt bound (p + k) then 1 - aNatOf av (p + k) else 0)

theorem missAbove_cast (av : Nat → Fp) (bound p : Nat)
    (hb : ∀ k, av k = 0 ∨ av k = 1) :
    missAbove av bound p = (missNat av bound p : Fp) := by
  unfold missAbove missNat
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  unfold missTerm
  by_cases h : bitAt bound (p + k) = true
  · rw [if_pos h, if_pos h, aNatOf_cast (hb (p + k)),
      Nat.cast_sub (aNatOf_le_one av (p + k)), Nat.cast_one]
  · rw [if_neg h, if_neg h]

/-- If the missing count above `p` vanishes, every ONE bit of `bound` at
position `≥ p` is matched. -/
theorem av_eq_one_of_missAbove_zero (av : Nat → Fp) (bound p : Nat)
    (hb : ∀ k, av k = 0 ∨ av k = 1) (h : missAbove av bound p = 0) :
    ∀ k, p ≤ k → k < 256 → bitAt bound k = true → av k = 1 := by
  rw [missAbove_cast av bound p hb] at h
  have hle : missNat av bound p ≤ 256 := by
    have h1 : missNat av bound p ≤ ∑ _k ∈ Finset.range (256 - p), 1 := by
      unfold missNat
      apply Finset.sum_le_sum
      intro k _
      split
      · have := aNatOf_le_one av (p + k); omega
      · omega
    have h2 : (∑ _k ∈ Finset.range (256 - p), 1) = 256 - p := by simp
    omega
  have hprime : (256 : Nat) < circuitPrime := by decide
  have h0 : missNat av bound p = 0 := by
    rw [ZMod.natCast_eq_zero_iff] at h
    exact Nat.eq_zero_of_dvd_of_lt h (by omega)
  intro k hk1 hk2 hbk
  have hmem : k - p ∈ Finset.range (256 - p) := Finset.mem_range.mpr (by omega)
  have hz := (Finset.sum_eq_zero_iff.mp h0) (k - p) hmem
  rw [show p + (k - p) = k from by omega, if_pos hbk] at hz
  have hb1 := aNatOf_le_one av k
  have h1 : aNatOf av k = 1 := by omega
  rcases hb k with h' | h'
  · simp [aNatOf, h'] at h1
  · exact h'

/-- Above a zero run with vanishing missing count, the bits agree with `bound`. -/
theorem agree_of_miss_zero (av : Nat → Fp) (bound p q : Nat)
    (hb : ∀ k, av k = 0 ∨ av k = 1)
    (hmiss : missAbove av bound p = 0)
    (hzero : ∀ k, q ≤ k → k < p → bitAt bound k = false)
    (hpref : prefVal (boundNat bound) 256 = bound)
    (hle : prefVal (fun j => aNatOf av (255 - j)) 256 ≤ bound) :
    ∀ j, j < 256 - q → aNatOf av (255 - j) = boundNat bound j := by
  have hone := av_eq_one_of_missAbove_zero av bound p hb hmiss
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
      intro hj
      have hk2 : 255 - j < 256 := by omega
      by_cases hbnd : bitAt bound (255 - j) = true
      · have hk1 : p ≤ 255 - j := by
          by_contra hlt
          have := hzero (255 - j) (by omega) (by omega)
          rw [this] at hbnd; exact absurd hbnd (by simp)
        have hbn : boundNat bound j = 1 := by simp [boundNat, bBit, hbnd]
        rw [hbn]
        simp [aNatOf, hone (255 - j) hk1 hk2 hbnd]
      · have hbnd' : bitAt bound (255 - j) = false := by simpa using hbnd
        have hbn : boundNat bound j = 0 := by simp [boundNat, bBit, hbnd']
        rw [hbn]
        by_contra hne
        have hav : av (255 - j) = 1 := by
          rcases hb (255 - j) with h' | h'
          · simp [aNatOf, h'] at hne
          · exact h'
        have hx : aNatOf av (255 - j) = 1 := by simp [aNatOf, hav]
        have hcongr : prefVal (fun j' => aNatOf av (255 - j')) j =
            prefVal (boundNat bound) j := by
          apply prefVal_congr
          intro j' hj'
          exact ih j' hj' (by omega)
        have hlt : prefVal (boundNat bound) (j + 1) <
            prefVal (fun j' => aNatOf av (255 - j')) (j + 1) := by
          simp only [prefVal, hcongr, hx, hbn]
          omega
        have h2 := prefVal_lt_of_lt (m := j + 1) (by omega) hlt
          (fun j' _ _ => by simp only [boundNat]; split <;> omega)
        rw [hpref] at h2
        omega

/-- A run sum vanishes when every bit of the run is zero. -/
theorem runSumVal_eq_zero_of_bits (av : Nat → Fp) (hi lo : Nat) (h : lo ≤ hi)
    (hb : ∀ k, lo ≤ k → k ≤ hi → av k = 0) : runSumVal av hi lo = 0 := by
  unfold runSumVal
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finset.mem_range] at hj
  exact hb (hi - j) (by omega) (by omega)

/-- On a zero run whose missing count vanishes, every bit is zero. -/
theorem run_bits_zero (av : Nat → Fp) (bound : Nat) (r : Nat × Nat × Bool)
    (hbits : ∀ k, r.2.1 ≤ k → k ≤ r.1 → bitAt bound k = r.2.2)
    (hrf : r.2.2 = false) (hhi : r.1 ≤ 255)
    (hb : ∀ k, av k = 0 ∨ av k = 1)
    (hmiss : missAbove av bound (r.1 + 1) = 0)
    (hpref : prefVal (boundNat bound) 256 = bound)
    (hle : prefVal (fun j => aNatOf av (255 - j)) 256 ≤ bound) :
    ∀ k, r.2.1 ≤ k → k ≤ r.1 → av k = 0 := by
  have hagree := agree_of_miss_zero av bound (r.1 + 1) r.2.1 hb hmiss
    (fun k h1 h2 => (hbits k h1 (by omega)).trans hrf) hpref hle
  intro k h1 h2
  have hk : 255 - k < 256 - r.2.1 := by omega
  have h := hagree (255 - k) hk
  have hbn : boundNat bound (255 - k) = 0 := by
    have hb1 : bBit bound (255 - k) = false := by
      unfold bBit
      rw [show 255 - (255 - k) = k from by omega, hbits k h1 h2, hrf]
    simp [boundNat, hb1]
  rw [hbn] at h
  have hk' : 255 - (255 - k) = k := by omega
  rw [hk'] at h
  rcases hb k with h' | h'
  · exact h'
  · simp [aNatOf, h'] at h

/-- The missing count vanishes when every ONE bit above `p` is matched. -/
theorem missAbove_eq_zero (av : Nat → Fp) (bound p : Nat)
    (h : ∀ k, p ≤ k → k < 256 → bitAt bound k = true → av k = 1) :
    missAbove av bound p = 0 := by
  unfold missAbove
  apply Finset.sum_eq_zero
  intro k hk
  simp only [Finset.mem_range] at hk
  unfold missTerm
  by_cases hb : bitAt bound (p + k) = true
  · rw [if_pos hb, h (p + k) (by omega) (by omega) hb, sub_self]
  · rw [if_neg hb]

end StandardECDSA.Gadgets
