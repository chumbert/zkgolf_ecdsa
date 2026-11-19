/-
# Semantic specs for the constant-bound comparators

`assertLtOrderOf bound a` asserts `a ≤ bound` for Boolean bits `a` (least
significant first); `assertLtOrderGuardedOf bound guard a` asserts
`guard = 1 → a ≤ bound`.

The rows are one product per maximal ZERO run of `bound`:

```text
missing * quotient = sum
```

`Math/Compare.lean` supplies the arithmetic.  This module connects the rows to
it:

* `ltLoop_rows` is the loop invariant: at every zero run the `missing` factor is
  exactly the number of missing ONE bits of `bound` above the run;
* `assertLtOrderOf_sound` concludes `prefVal x 256 ≤ bound`;
* `assertLtOrderGuardedOf_sound` concludes the same under `guard = 1`, and is
  vacuous when `guard = 0` because the first factor is then `missing + 1 ≥ 1`.

Task T06 (semantic half) / T07.
-/

import StandardECDSA.Math.Compare
import StandardECDSA.Gadgets.MatExplicit

set_option maxRecDepth 100000

namespace StandardECDSA.Gadgets

open StandardECDSA.Math
open Challenge.Instances.ECDSA_P256_Digest.Interface

/-! ## The loop invariant -/

/-- At every zero run of `bound`, the `missing` factor used by the row is the
number of missing ONE bits of `bound` above the run, and the row says that this
count times some quotient is the run sum. -/
theorem ltLoop_rows (env : Environment Fp) (av : Nat → Fp) (a : Nat → E)
    (ha : ∀ k, Expression.eval env (a k) = av k) (bound : Nat) :
    ∀ (l : List (Nat × Nat × Bool)) (p : Nat) (m : E) (n : Nat),
      p ≤ 256 →
      RunsCover bound p l →
      Expression.eval env m = missAbove av bound p →
      ConstraintsHold.Soundness env ((ltLoop a m l).operations n) →
      ∀ r ∈ l, r.2.2 = false →
        ∃ q, missAbove av bound (r.1 + 1) * q = runSumVal av r.1 r.2.1 := by
  intro l
  induction l with
  | nil => intro p m n _ _ _ _ r hr; simp at hr
  | cons s rest ih =>
      intro p m n hp hcov hm hrows r hr hf
      obtain ⟨hi, lo, bit⟩ := s
      simp only [RunsCover, RunsCoverB, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hcov
      obtain ⟨⟨⟨hhead, hle⟩, hbits⟩, hrest⟩ := hcov
      subst hhead
      have hbits' : ∀ k, lo ≤ k → k ≤ hi → bitAt bound k = bit := by
        intro k h1 h2
        have hmem : k - lo ∈ List.range (hi + 1 - lo) := List.mem_range.mpr (by omega)
        have hh := List.all_eq_true.mp hbits (k - lo) hmem
        simp only [beq_iff_eq] at hh
        rwa [Nat.add_sub_cancel' h1] at hh
      unfold ltLoop at hrows
      by_cases hb : bit
      · rw [if_pos hb] at hrows
        have hbT : ∀ k, lo ≤ k → k ≤ hi → bitAt bound k = true := by
          intro k h1 h2; rw [hbits' k h1 h2]; exact hb
        have hmr := missRunVal_of_bits av bound hi lo true hbT
        simp only [if_true] at hmr
        have hsplit := missAbove_split av bound lo (hi + 1) (by omega) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at hsplit
        have hnew : Expression.eval env (addMissing a hi lo m) = missAbove av bound lo := by
          rw [eval_addMissing env av a ha, hm, hsplit, hmr,
            add_comm (missAbove av bound (hi + 1)), add_left_inj]
          have e1 : hi + 1 - lo = hi - lo + 1 := by omega
          rw [e1, ← sum_range_reflect' (fun k => 1 - av k) hi lo (by omega)]
        rcases List.mem_cons.mp hr with rfl | hr'
        · rw [hb] at hf; exact absurd hf (by simp)
        · exact ih lo _ n (by omega) hrest hnew hrows r hr' hf
      · rw [if_neg hb] at hrows
        simp only [Bool.not_eq_true] at hb
        simp only [bind_snd, witnessField_snd, assertZero_snd, List.nil_append,
          List.append_nil, Operations.localLength, List.sum_cons, List.sum_nil,
          Nat.add_zero, ConstraintsHold.Soundness] at hrows
        rw [Operations.forAllNoOffset_append, Operations.forAllNoOffset_append] at hrows
        obtain ⟨-, h2, h3⟩ := hrows
        have hrow : Expression.eval env (pm m (.var ⟨n⟩) - runSum a hi lo) = 0 := h2.1
        have hbF : ∀ k, lo ≤ k → k ≤ hi → bitAt bound k = false := by
          intro k h1 h2; rw [hbits' k h1 h2]; exact hb
        have hmr := missRunVal_of_bits av bound hi lo false hbF
        simp only [if_false, Bool.false_eq_true] at hmr
        have hsplit := missAbove_split av bound lo (hi + 1) (by omega) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at hsplit
        have hsame : Expression.eval env m = missAbove av bound lo := by
          rw [hm, hsplit, hmr, zero_add]
        have hprod : Expression.eval env m * Expression.eval env (.var ⟨n⟩) =
            runSumVal av hi lo := by
          have h := hrow
          simp only [circuit_norm, pm, eval_runSum env av a ha] at h
          rw [sub_eq_zero] at h
          exact h
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact ⟨Expression.eval env (.var ⟨n⟩), by rw [← hm]; exact hprod⟩
        · exact ih lo _ (n + 1) (by omega) hrest hsame h3 r hr' hf

/-! ## The guarded loop invariant -/

/-- The guarded loop's rows, under `guard = 1`. -/
theorem ltLoopGuarded_rows (env : Environment Fp) (av : Nat → Fp) (a : Nat → E)
    (ha : ∀ k, Expression.eval env (a k) = av k) (bound : Nat) (guard : E)
    (hg : Expression.eval env guard = 1) :
    ∀ (l : List (Nat × Nat × Bool)) (p : Nat) (m : E) (n : Nat),
      p ≤ 256 →
      RunsCover bound p l →
      Expression.eval env m = missAbove av bound p →
      ConstraintsHold.Soundness env ((ltLoopGuarded a guard m l).operations n) →
      ∀ r ∈ l, r.2.2 = false →
        ∃ q, missAbove av bound (r.1 + 1) * q = runSumVal av r.1 r.2.1 := by
  intro l
  induction l with
  | nil => intro p m n _ _ _ _ r hr; simp at hr
  | cons s rest ih =>
      intro p m n hp hcov hm hrows r hr hf
      obtain ⟨hi, lo, bit⟩ := s
      simp only [RunsCover, RunsCoverB, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hcov
      obtain ⟨⟨⟨hhead, hle⟩, hbits⟩, hrest⟩ := hcov
      subst hhead
      have hbits' : ∀ k, lo ≤ k → k ≤ hi → bitAt bound k = bit := by
        intro k h1 h2
        have hmem : k - lo ∈ List.range (hi + 1 - lo) := List.mem_range.mpr (by omega)
        have hh := List.all_eq_true.mp hbits (k - lo) hmem
        simp only [beq_iff_eq] at hh
        rwa [Nat.add_sub_cancel' h1] at hh
      unfold ltLoopGuarded at hrows
      by_cases hb : bit
      · rw [if_pos hb] at hrows
        have hbT : ∀ k, lo ≤ k → k ≤ hi → bitAt bound k = true := by
          intro k h1 h2; rw [hbits' k h1 h2]; exact hb
        have hmr := missRunVal_of_bits av bound hi lo true hbT
        simp only [if_true] at hmr
        have hsplit := missAbove_split av bound lo (hi + 1) (by omega) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at hsplit
        have hnew : Expression.eval env (addMissing a hi lo m) = missAbove av bound lo := by
          rw [eval_addMissing env av a ha, hm, hsplit, hmr,
            add_comm (missAbove av bound (hi + 1)), add_left_inj]
          have e1 : hi + 1 - lo = hi - lo + 1 := by omega
          rw [e1, ← sum_range_reflect' (fun k => 1 - av k) hi lo (by omega)]
        rcases List.mem_cons.mp hr with rfl | hr'
        · rw [hb] at hf; exact absurd hf (by simp)
        · exact ih lo _ n (by omega) hrest hnew hrows r hr' hf
      · rw [if_neg hb] at hrows
        simp only [Bool.not_eq_true] at hb
        simp only [bind_snd, witnessField_snd, assertZero_snd, List.append_nil,
          Operations.localLength, List.sum_cons, List.sum_nil,
          Nat.add_zero, ConstraintsHold.Soundness] at hrows
        rw [Operations.forAllNoOffset_append, Operations.forAllNoOffset_append] at hrows
        obtain ⟨-, h2, h3⟩ := hrows
        have hrow : Expression.eval env
            (pm (m + (cst 1 - guard)) (.var ⟨n⟩) - runSum a hi lo) = 0 := h2.1
        have hbF : ∀ k, lo ≤ k → k ≤ hi → bitAt bound k = false := by
          intro k h1 h2; rw [hbits' k h1 h2]; exact hb
        have hmr := missRunVal_of_bits av bound hi lo false hbF
        simp only [if_false, Bool.false_eq_true] at hmr
        have hsplit := missAbove_split av bound lo (hi + 1) (by omega) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at hsplit
        have hsame : Expression.eval env m = missAbove av bound lo := by
          rw [hm, hsplit, hmr, zero_add]
        have hprod : Expression.eval env m * Expression.eval env (.var ⟨n⟩) =
            runSumVal av hi lo := by
          have h := hrow
          simp only [circuit_norm, pm, eval_runSum env av a ha, cst, hg, sub_self,
            add_zero] at h
          rw [sub_eq_zero] at h
          exact h
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact ⟨Expression.eval env (.var ⟨n⟩), by rw [← hm]; exact hprod⟩
        · exact ih lo _ (n + 1) (by omega) hrest hsame h3 r hr' hf

/-! ## Soundness of the comparators -/

/-- Soundness of `assertLtOrderOf`: Boolean bits satisfying the rows spell at
most `bound`. -/
theorem assertLtOrderOf_sound (bound : Nat) (a : Nat → E) (env : Environment Fp) (n : Nat)
    (hrows : ConstraintsHold.Soundness env ((assertLtOrderOf bound a).operations n))
    (hbool : ∀ k < 256, Expression.eval env (a k) = 0 ∨ Expression.eval env (a k) = 1)
    (hpref : prefVal (boundNat bound) 256 = bound)
    (hcover : RunsCover bound 256 (boundRunsOf bound)) :
    prefVal (fun j => aNatOf (fun k => Expression.eval env (a k)) (255 - j)) 256 ≤ bound := by
  refine prefVal_le_of_runs bound _ (fun j _ => aNatOf_le_one _ _) hpref hcover ?_
  intro r hr hrf hpre j h1 h2
  have hmiss : missAbove (fun k => Expression.eval env (a k)) bound (r.1 + 1) = 0 := by
    apply missAbove_eq_zero
    intro k hk1 hk2 hbk
    have hj : 255 - k < 255 - r.1 := by omega
    have hbj : bBit bound (255 - k) = true := by
      unfold bBit
      rw [show 255 - (255 - k) = k from by omega]
      exact hbk
    have hh := hpre (255 - k) hj hbj
    have hkk : 255 - (255 - k) = k := by omega
    rw [hkk] at hh
    unfold aNatOf at hh
    by_cases hv : Expression.eval env (a k) = 1
    · exact hv
    · rw [if_neg hv] at hh
      exact absurd hh (by simp)
  have hm0 : Expression.eval env (cst 0) =
      missAbove (fun k => Expression.eval env (a k)) bound 256 := by
    simp only [circuit_norm, cst]
    unfold missAbove
    simp
  obtain ⟨q, hq⟩ := ltLoop_rows env (fun k => Expression.eval env (a k)) a (fun k => rfl)
    bound (boundRunsOf bound) 256 (cst 0) n (by omega) hcover hm0 hrows r hr hrf
  rw [hmiss, zero_mul] at hq
  have hz := runSumVal_eq_zero _ r.1 r.2.1 (RunsCover.le hcover r hr)
    (by have := RunsCover.hi_lt hcover r hr; omega)
    (fun k hk1 hk2 => hbool k (by have := RunsCover.hi_lt hcover r hr; omega))
    hq.symm
  have hlo255 : r.2.1 ≤ 255 := by
    have h1 := RunsCover.hi_lt hcover r hr
    have h2 := RunsCover.le hcover r hr
    omega
  have hk : 255 - j ≤ r.1 := by omega
  have hk' : r.2.1 ≤ 255 - j := by omega
  have hfin := hz (255 - j) hk' hk
  simp only [aNatOf, hfin]
  simp

/-- Soundness of `assertLtOrderGuardedOf`: when `guard = 1`, Boolean bits
satisfying the rows spell at most `bound`. -/
theorem assertLtOrderGuardedOf_sound (bound : Nat) (guard : E) (a : Nat → E)
    (env : Environment Fp) (n : Nat)
    (hrows : ConstraintsHold.Soundness env ((assertLtOrderGuardedOf bound guard a).operations n))
    (hg : Expression.eval env guard = 1)
    (hbool : ∀ k < 256, Expression.eval env (a k) = 0 ∨ Expression.eval env (a k) = 1)
    (hpref : prefVal (boundNat bound) 256 = bound)
    (hcover : RunsCover bound 256 (boundRunsOf bound)) :
    prefVal (fun j => aNatOf (fun k => Expression.eval env (a k)) (255 - j)) 256 ≤ bound := by
  refine prefVal_le_of_runs bound _ (fun j _ => aNatOf_le_one _ _) hpref hcover ?_
  intro r hr hrf hpre j h1 h2
  have hmiss : missAbove (fun k => Expression.eval env (a k)) bound (r.1 + 1) = 0 := by
    apply missAbove_eq_zero
    intro k hk1 hk2 hbk
    have hj : 255 - k < 255 - r.1 := by omega
    have hbj : bBit bound (255 - k) = true := by
      unfold bBit
      rw [show 255 - (255 - k) = k from by omega]
      exact hbk
    have hh := hpre (255 - k) hj hbj
    have hkk : 255 - (255 - k) = k := by omega
    rw [hkk] at hh
    unfold aNatOf at hh
    by_cases hv : Expression.eval env (a k) = 1
    · exact hv
    · rw [if_neg hv] at hh
      exact absurd hh (by simp)
  have hm0 : Expression.eval env (cst 0) =
      missAbove (fun k => Expression.eval env (a k)) bound 256 := by
    simp only [circuit_norm, cst]
    unfold missAbove
    simp
  obtain ⟨q, hq⟩ := ltLoopGuarded_rows env (fun k => Expression.eval env (a k)) a (fun k => rfl)
    bound guard hg (boundRunsOf bound) 256 (cst 0) n (by omega) hcover hm0 hrows r hr hrf
  rw [hmiss, zero_mul] at hq
  have hz := runSumVal_eq_zero _ r.1 r.2.1 (RunsCover.le hcover r hr)
    (by have := RunsCover.hi_lt hcover r hr; omega)
    (fun k hk1 hk2 => hbool k (by have := RunsCover.hi_lt hcover r hr; omega))
    hq.symm
  have hlo255 : r.2.1 ≤ 255 := by
    have h1 := RunsCover.hi_lt hcover r hr
    have h2 := RunsCover.le hcover r hr
    omega
  have hk : 255 - j ≤ r.1 := by omega
  have hk' : r.2.1 ≤ 255 - j := by omega
  have hfin := hz (255 - j) hk' hk
  simp only [aNatOf, hfin]
  simp

/-! ## Completeness of the comparators -/

/-- Completeness of the comparison loop. -/
theorem ltLoop_complete (env : ProverEnvironment Fp) (av : Nat → Fp) (a : Nat → E)
    (ha : ∀ k, Expression.eval env.toEnvironment (a k) = av k)
    (hb : ∀ k, av k = 0 ∨ av k = 1)
    (bound : Nat) (hpref : prefVal (boundNat bound) 256 = bound)
    (hle : prefVal (fun j => aNatOf av (255 - j)) 256 ≤ bound) :
    ∀ (l : List (Nat × Nat × Bool)) (p : Nat) (m : E) (n : Nat),
      p ≤ 256 → RunsCover bound p l →
      Expression.eval env.toEnvironment m = missAbove av bound p →
      env.UsesLocalWitnessesCompleteness n ((ltLoop a m l).operations n) →
      ConstraintsHold.Completeness env ((ltLoop a m l).operations n) := by
  intro l
  induction l with
  | nil =>
      intro p m n _ _ _ _
      simp only [ltLoop, Circuit.operations, pure_snd, ConstraintsHold.Completeness,
        Operations.forAllNoOffset]
  | cons s rest ih =>
      intro p m n hp hcov hm hulwc
      obtain ⟨hi, lo, bit⟩ := s
      simp only [RunsCover, RunsCoverB, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hcov
      obtain ⟨⟨⟨hhead, hlerun⟩, hbits⟩, hrest⟩ := hcov
      subst hhead
      have hbits' : ∀ k, lo ≤ k → k ≤ hi → bitAt bound k = bit := by
        intro k h1 h2
        have hmem : k - lo ∈ List.range (hi + 1 - lo) := List.mem_range.mpr (by omega)
        have hh := List.all_eq_true.mp hbits (k - lo) hmem
        simp only [beq_iff_eq] at hh
        rwa [Nat.add_sub_cancel' h1] at hh
      unfold ltLoop at hulwc ⊢
      by_cases hb' : bit
      · rw [if_pos hb'] at hulwc ⊢
        have hbT : ∀ k, lo ≤ k → k ≤ hi → bitAt bound k = true := by
          intro k h1 h2; rw [hbits' k h1 h2]; exact hb'
        have hmr := missRunVal_of_bits av bound hi lo true hbT
        simp only [if_true] at hmr
        have hsplit := missAbove_split av bound lo (hi + 1) (by omega) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at hsplit
        have hnew : Expression.eval env.toEnvironment (addMissing a hi lo m) =
            missAbove av bound lo := by
          rw [eval_addMissing env.toEnvironment av a ha, hm, hsplit, hmr,
            add_comm (missAbove av bound (hi + 1)), add_left_inj]
          have e1 : hi + 1 - lo = hi - lo + 1 := by omega
          rw [e1, ← sum_range_reflect' (fun k => 1 - av k) hi lo (by omega)]
        exact ih lo _ n (by omega) hrest hnew hulwc
      · rw [if_neg hb'] at hulwc ⊢
        simp only [Bool.not_eq_true] at hb'
        simp only [bind_snd, witnessField_snd, assertZero_snd, Operations.localLength,
          List.sum_cons, List.sum_nil, Nat.add_zero] at hulwc ⊢
        unfold ProverEnvironment.UsesLocalWitnessesCompleteness at hulwc
        obtain ⟨hwit, hulwc'⟩ := hulwc
        have hbF : ∀ k, lo ≤ k → k ≤ hi → bitAt bound k = false := by
          intro k h1 h2; rw [hbits' k h1 h2]; exact hb'
        have hmr := missRunVal_of_bits av bound hi lo false hbF
        simp only [if_false, Bool.false_eq_true] at hmr
        have hsplit := missAbove_split av bound lo (hi + 1) (by omega) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at hsplit
        have hsame : Expression.eval env.toEnvironment m = missAbove av bound lo := by
          rw [hm, hsplit, hmr, zero_add]
        simp only [ConstraintsHold.Completeness, Operations.forAllNoOffset_append,
          Operations.forAllNoOffset_append, Operations.forAllNoOffset, and_true]
        refine ⟨trivial, ?_, ?_⟩
        · have hw := hwit ⟨0, by simp⟩
          rw [Witgen.WitgenIR.getElem_eval_ofFExpr] at hw
          simp only [Witgen.FExpr.eval, Nat.add_zero] at hw
          have hsum : Expression.eval env.toEnvironment (runSum a hi lo) = runSumVal av hi lo :=
            eval_runSum env.toEnvironment av a ha hi lo
          simp only [circuit_norm, pm] at hw ⊢
          by_cases hzero : Expression.eval env.toEnvironment m = 0
          · have hz := run_bits_zero av bound (hi, lo, bit) hbits' hb' (by omega) hb
              (by rw [← hm]; exact hzero) hpref hle
            have hsz : runSumVal av hi lo = 0 :=
              runSumVal_eq_zero_of_bits av hi lo (by omega) hz
            simp [hsum, hsz, hzero]
          · rw [hw]
            simp only [hsum]
            field_simp
            ring
        · have h := ih lo _ (n + 1) (by omega) hrest hsame hulwc'
          simpa [Circuit.operations, ConstraintsHold.Completeness] using h

/-! ## The guarded comparator: completeness on the inactive branch -/

/-- The missing-bit count is at most the number of positions. -/
theorem missNat_le (av : Nat → Fp) (bound p : Nat) : missNat av bound p ≤ 256 := by
  have h1 : missNat av bound p ≤ ∑ _k ∈ Finset.range (256 - p), 1 := by
    unfold missNat
    apply Finset.sum_le_sum
    intro k _
    split
    · have := aNatOf_le_one av (p + k); omega
    · omega
  have h2 : (∑ _k ∈ Finset.range (256 - p), 1) = 256 - p := by simp
  omega

/-- `missing + 1` never vanishes in the field: the count is a small natural. -/
theorem missAbove_add_one_ne_zero (av : Nat → Fp) (bound p : Nat)
    (hb : ∀ k, av k = 0 ∨ av k = 1) : missAbove av bound p + 1 ≠ 0 := by
  rw [missAbove_cast av bound p hb]
  intro h
  have hle := missNat_le av bound p
  have hprime : (257 : Nat) < circuitPrime := by decide
  have hcast : ((missNat av bound p : Fp) + 1) = ((missNat av bound p + 1 : Nat) : Fp) := by
    push_cast; ring
  rw [hcast, ZMod.natCast_eq_zero_iff] at h
  have hlt : missNat av bound p + 1 < circuitPrime := by omega
  have h0 := Nat.eq_zero_of_dvd_of_lt h hlt
  omega

/-- Completeness of the guarded comparison loop.  The inactive branch
(`guard = 0`) is complete because the first factor is then `missing + 1 ≥ 1`. -/
theorem ltLoopGuarded_complete (env : ProverEnvironment Fp) (av : Nat → Fp) (a : Nat → E)
    (ha : ∀ k, Expression.eval env.toEnvironment (a k) = av k)
    (hb : ∀ k, av k = 0 ∨ av k = 1)
    (bound : Nat) (guard : E)
    (hg : Expression.eval env.toEnvironment guard = 0 ∨
      Expression.eval env.toEnvironment guard = 1)
    (hpref : prefVal (boundNat bound) 256 = bound)
    (hle : Expression.eval env.toEnvironment guard = 1 →
      prefVal (fun j => aNatOf av (255 - j)) 256 ≤ bound) :
    ∀ (l : List (Nat × Nat × Bool)) (p : Nat) (m : E) (n : Nat),
      p ≤ 256 → RunsCover bound p l →
      Expression.eval env.toEnvironment m = missAbove av bound p →
      env.UsesLocalWitnessesCompleteness n ((ltLoopGuarded a guard m l).operations n) →
      ConstraintsHold.Completeness env ((ltLoopGuarded a guard m l).operations n) := by
  intro l
  induction l with
  | nil =>
      intro p m n _ _ _ _
      simp only [ltLoopGuarded, Circuit.operations, pure_snd, ConstraintsHold.Completeness,
        Operations.forAllNoOffset]
  | cons s rest ih =>
      intro p m n hp hcov hm hulwc
      obtain ⟨hi, lo, bit⟩ := s
      simp only [RunsCover, RunsCoverB, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hcov
      obtain ⟨⟨⟨hhead, hlerun⟩, hbits⟩, hrest⟩ := hcov
      subst hhead
      have hbits' : ∀ k, lo ≤ k → k ≤ hi → bitAt bound k = bit := by
        intro k h1 h2
        have hmem : k - lo ∈ List.range (hi + 1 - lo) := List.mem_range.mpr (by omega)
        have hh := List.all_eq_true.mp hbits (k - lo) hmem
        simp only [beq_iff_eq] at hh
        rwa [Nat.add_sub_cancel' h1] at hh
      unfold ltLoopGuarded at hulwc ⊢
      by_cases hb' : bit
      · rw [if_pos hb'] at hulwc ⊢
        have hbT : ∀ k, lo ≤ k → k ≤ hi → bitAt bound k = true := by
          intro k h1 h2; rw [hbits' k h1 h2]; exact hb'
        have hmr := missRunVal_of_bits av bound hi lo true hbT
        simp only [if_true] at hmr
        have hsplit := missAbove_split av bound lo (hi + 1) (by omega) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at hsplit
        have hnew : Expression.eval env.toEnvironment (addMissing a hi lo m) =
            missAbove av bound lo := by
          rw [eval_addMissing env.toEnvironment av a ha, hm, hsplit, hmr,
            add_comm (missAbove av bound (hi + 1)), add_left_inj]
          have e1 : hi + 1 - lo = hi - lo + 1 := by omega
          rw [e1, ← sum_range_reflect' (fun k => 1 - av k) hi lo (by omega)]
        exact ih lo _ n (by omega) hrest hnew hulwc
      · rw [if_neg hb'] at hulwc ⊢
        simp only [Bool.not_eq_true] at hb'
        simp only [bind_snd, witnessField_snd, assertZero_snd, Operations.localLength,
          List.sum_cons, List.sum_nil, Nat.add_zero] at hulwc ⊢
        unfold ProverEnvironment.UsesLocalWitnessesCompleteness at hulwc
        obtain ⟨hwit, hulwc'⟩ := hulwc
        have hbF : ∀ k, lo ≤ k → k ≤ hi → bitAt bound k = false := by
          intro k h1 h2; rw [hbits' k h1 h2]; exact hb'
        have hmr := missRunVal_of_bits av bound hi lo false hbF
        simp only [if_false, Bool.false_eq_true] at hmr
        have hsplit := missAbove_split av bound lo (hi + 1) (by omega) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at hsplit
        have hsame : Expression.eval env.toEnvironment m = missAbove av bound lo := by
          rw [hm, hsplit, hmr, zero_add]
        simp only [ConstraintsHold.Completeness, Operations.forAllNoOffset_append,
          Operations.forAllNoOffset_append, Operations.forAllNoOffset, and_true]
        refine ⟨trivial, ?_, ?_⟩
        · have hw := hwit ⟨0, by simp⟩
          rw [Witgen.WitgenIR.getElem_eval_ofFExpr] at hw
          simp only [Witgen.FExpr.eval, Nat.add_zero] at hw
          have hsum : Expression.eval env.toEnvironment (runSum a hi lo) = runSumVal av hi lo :=
            eval_runSum env.toEnvironment av a ha hi lo
          simp only [circuit_norm, pm] at hw ⊢
          have hc1 : Expression.eval env.toEnvironment (cst 1) = 1 := rfl
          by_cases hfac : Expression.eval env.toEnvironment m +
              (Expression.eval env.toEnvironment (cst 1) -
                Expression.eval env.toEnvironment guard) = 0
          · have hg1 : Expression.eval env.toEnvironment guard = 1 := by
              rcases hg with h0 | h1
              · exfalso
                apply missAbove_add_one_ne_zero av bound (hi + 1) hb
                rw [hm, h0, hc1] at hfac
                simpa using hfac
              · exact h1
            have hm0 : Expression.eval env.toEnvironment m = 0 := by
              rw [hg1, hc1] at hfac
              simpa using hfac
            have hz := run_bits_zero av bound (hi, lo, bit) hbits' hb' (by omega) hb
              (by rw [← hm]; exact hm0) hpref (hle hg1)
            have hsz : runSumVal av hi lo = 0 :=
              runSumVal_eq_zero_of_bits av hi lo (by omega) hz
            simp [hfac, hsum, hsz]
          · rw [hw]
            simp only [hsum]
            field_simp
            ring_nf
        · have h := ih lo _ (n + 1) (by omega) hrest hsame hulwc'
          simpa [Circuit.operations, ConstraintsHold.Completeness] using h

end StandardECDSA.Gadgets
