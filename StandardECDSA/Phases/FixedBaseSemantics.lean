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

/-! ## Additivity of the projective-to-affine map -/

set_option maxRecDepth 10000 in
theorem toAffineLift_add (P Q : (params.toMathlib).toProjective.Point) :
    WeierstrassCurve.Projective.Point.toAffineLift (P + Q)
      = WeierstrassCurve.Projective.Point.toAffineLift P
        + WeierstrassCurve.Projective.Point.toAffineLift Q :=
  WeierstrassCurve.Projective.Point.toAffineLift_add (W := params.toMathlib) P Q

theorem toAffineLift_zero :
    WeierstrassCurve.Projective.Point.toAffineLift
      (0 : (params.toMathlib).toProjective.Point) = 0 :=
  WeierstrassCurve.Projective.Point.toAffineLift_zero

/-! ## The window digit and the window sum -/

/-- The window digit `d_i = eBit[2i] + 2·eBit[2i+1]` read off the environment. -/
noncomputable def digitOf (env : Environment Fp) (eb : Vector E 256) (i : Nat) : Nat :=
  (Expression.eval env (eb.get ⟨2 * i % 256, Nat.mod_lt _ (by norm_num)⟩)).val
    + 2 * (Expression.eval env (eb.get ⟨(2 * i + 1) % 256, Nat.mod_lt _ (by norm_num)⟩)).val

theorem digitOf_eq (env : Environment Fp) (eb : Vector E 256) (k : Nat) (hk : k < 128) :
    digitOf env eb k
      = (Expression.eval env (eb.get ⟨2 * k, by omega⟩)).val
        + 2 * (Expression.eval env (eb.get ⟨2 * k + 1, by omega⟩)).val := by
  simp only [digitOf, Nat.mod_eq_of_lt (by omega : 2 * k < 256),
    Nat.mod_eq_of_lt (by omega : 2 * k + 1 < 256)]

/-- The fixed-base window sum after `k` windows. -/
noncomputable def winSum (env : Environment Fp) (eb : Vector E 256) (k : Nat) : Nat :=
  ∑ i ∈ Finset.range k, (4 + digitOf env eb i) * 4 ^ i

theorem winSum_succ (env : Environment Fp) (eb : Vector E 256) (k : Nat) :
    winSum env eb (k + 1) = winSum env eb k + (4 + digitOf env eb k) * 4 ^ k := by
  simp only [winSum, Finset.sum_range_succ]

/-- The digest `E = leNat eBit` read off the environment. -/
noncomputable def digestNat (env : Environment Fp) (eb : Vector E 256) : Nat :=
  leNat (k := 256) (fun j => (Expression.eval env (eb.get j)).val)

/-- **Window sum at 128.**  The 128 window constants sum to the shift plus the
digest `E = leNat eBit`. -/
theorem winSum_128 (env : Environment Fp) (eb : Vector E 256) :
    winSum env eb 128 = shiftNat + digestNat env eb := by
  have h1 : (∑ i ∈ Finset.range 128, digitOf env eb i * 4 ^ i) = digestNat env eb := by
    rw [digestNat, ← window_digit_sum (fun j => (Expression.eval env (eb.get j)).val)]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [digitOf, windowDigit, Nat.mod_eq_of_lt (by omega : 2 * i < 256),
      Nat.mod_eq_of_lt (by omega : 2 * i + 1 < 256)]
  simp only [winSum, window_sum, h1]

/-! ## The fixed-base invariant -/

/-- The constant mux of window `i`. -/
def fbMux (eb : Vector E 256) (tables : Array (Array (Fp × Fp))) (i : Fin 128) : C Pt :=
  muxConst4W (eb.get ⟨2 * i.val, by omega⟩) (eb.get ⟨2 * i.val + 1, by omega⟩)
    (tables.getD i.val #[])

theorem fixedBaseBody_eq (eb : Vector E 256) (tables : Array (Array (Fp × Fp)))
    (ep : Pt) (i : Fin 128) :
    fixedBaseBody eb tables ep i = (fbMux eb tables i >>= fun t => affAdd ep t) := rfl

/-- The fixed-base prefix invariant of plan §5. -/
noncomputable def fbInv (env : Environment Fp) (eb : Vector E 256) (Hpt : Affine.Point Wp)
    (k : Nat) (acc : Pt) : Prop :=
  ∃ hns : NS (Expression.eval env acc.1) (Expression.eval env acc.2),
    Affine.Point.some (Expression.eval env acc.1) (Expression.eval env acc.2) hns
      = Hpt + -shiftPt
        + WeierstrassCurve.Projective.Point.toAffineLift (winSum env eb k • Gpt)

/-- Generic invariant induction for `Fin.foldl`. -/
theorem fin_foldl_inv {α : Type} {m : Nat} (f : α → Fin m → α) (init : α)
    (P : Nat → α → Prop) (h0 : P 0 init)
    (hstep : ∀ (j : Nat) (hj : j < m) (acc : α), P j acc → P (j + 1) (f acc ⟨j, hj⟩)) :
    ∀ (k : Nat) (hk : k ≤ m),
      P k (Fin.foldl k (fun acc (i : Fin k) => f acc ⟨i.val, by omega⟩) init) := by
  intro k
  induction k with
  | zero => intro _; simpa using h0
  | succ k ih =>
    intro hk
    rw [Fin.foldl_succ_last]
    exact hstep k (by omega) _ (ih (by omega))

theorem foldlAcc_eq (env : Environment Fp) (eb : Vector E 256)
    (tables : Array (Array (Fp × Fp))) (init : Pt) (n : Nat) (k : Nat) (hk : k < 128) :
    Circuit.FoldlM.foldlAcc n (Vector.finRange 128) (fixedBaseBody eb tables) init ⟨k, hk⟩
      = Fin.foldl k (fun acc (i : Fin k) =>
          (fixedBaseBody eb tables acc ⟨i.val, by omega⟩).output (n + i.val * 5)) init := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]
  congr 1

theorem fixedTables_getD_row (k : Nat) (hk : k < 128) :
    fixedTables.getD k #[] = fbTab k hk := by
  have hs : k < fixedTables.size := by rw [fixedTables_size]; exact hk
  simp only [Array.getD, dif_pos hs, fbTab]
  rfl

/-- One fixed-base window preserves the prefix invariant. -/
theorem fbStep (env : Environment Fp) (eb : Vector E 256) (Hpt : Affine.Point Wp)
    (n k : Nat) (hk : k < 128) (acc : Pt)
    (hb0 : Expression.eval env (eb.get ⟨2 * k, by omega⟩) = 0
        ∨ Expression.eval env (eb.get ⟨2 * k, by omega⟩) = 1)
    (hb1 : Expression.eval env (eb.get ⟨2 * k + 1, by omega⟩) = 0
        ∨ Expression.eval env (eb.get ⟨2 * k + 1, by omega⟩) = 1)
    (hdx : Expression.eval env ((fbMux eb fixedTables ⟨k, hk⟩).output (n + k * 5)).1
        - Expression.eval env acc.1 ≠ 0)
    (hacc : fbInv env eb Hpt k acc)
    (hc : ConstraintsHold.Soundness env
      ((fixedBaseBody eb fixedTables acc ⟨k, hk⟩).operations (n + k * 5))) :
    fbInv env eb Hpt (k + 1) ((fixedBaseBody eb fixedTables acc ⟨k, hk⟩).output (n + k * 5)) := by
  obtain ⟨hns, hval⟩ := hacc
  rw [fixedBaseBody_eq] at hc ⊢
  obtain ⟨hc1, hc2⟩ := soundness_bind env (fbMux eb fixedTables ⟨k, hk⟩)
    (fun t => affAdd acc t) (n + k * 5) hc
  have hml : (fbMux eb fixedTables ⟨k, hk⟩).localLength (n + k * 5) = 1 := by
    simp only [fbMux]
    exact muxConst4W_localLength _ _ _ _
  rw [hml] at hc2
  -- the mux row
  have hrow : Expression.eval env (pm (eb.get ⟨2 * k, by omega⟩)
      (eb.get ⟨2 * k + 1, by omega⟩) - Expression.var (F := Fp) ⟨n + k * 5⟩) = 0 := by
    simp only [fbMux, fixedTables_getD_row k hk, muxConst4W, circuit_norm] at hc1
    simpa only [circuit_norm] using hc1
  obtain ⟨hT0, hTval0⟩ := muxConst4W_tablePt env k hk (eb.get ⟨2 * k, by omega⟩)
    (eb.get ⟨2 * k + 1, by omega⟩) (n + k * 5) hb0 hb1 hrow
  have hT : NS (Expression.eval env ((fbMux eb fixedTables ⟨k, hk⟩).output (n + k * 5)).1)
      (Expression.eval env ((fbMux eb fixedTables ⟨k, hk⟩).output (n + k * 5)).2) := by
    simp only [fbMux, fixedTables_getD_row k hk]
    exact hT0
  have hTval : Affine.Point.some (Expression.eval env ((fbMux eb fixedTables ⟨k, hk⟩).output
      (n + k * 5)).1) (Expression.eval env ((fbMux eb fixedTables ⟨k, hk⟩).output
      (n + k * 5)).2) hT
      = tablePt k ((Expression.eval env (eb.get ⟨2 * k, by omega⟩)).val
        + 2 * (Expression.eval env (eb.get ⟨2 * k + 1, by omega⟩)).val) := by
    simp only [fbMux, fixedTables_getD_row k hk]
    exact hTval0
  -- the affine addition
  obtain ⟨hR, hRval⟩ := affAdd_sound env acc ((fbMux eb fixedTables ⟨k, hk⟩).output (n + k * 5))
    (n + k * 5 + 1) hns hT hdx hc2
  -- output coordinates
  have hout : (fbMux eb fixedTables ⟨k, hk⟩ >>= fun t => affAdd acc t).output (n + k * 5)
      = (Expression.var (F := Fp) ⟨n + k * 5 + 3⟩, Expression.var (F := Fp) ⟨n + k * 5 + 4⟩) := by
    simp only [Circuit.output, bind_snd, affAdd_output, hml, Nat.add_zero]
    rfl
  rw [hout]
  refine ⟨hR, ?_⟩
  refine hRval.trans ?_
  · have hd : digitOf env eb k
        = (Expression.eval env (eb.get ⟨2 * k, by omega⟩)).val
          + 2 * (Expression.eval env (eb.get ⟨2 * k + 1, by omega⟩)).val :=
      digitOf_eq env eb k hk
    have hTval' : Affine.Point.some (Expression.eval env ((fbMux eb fixedTables ⟨k, hk⟩).output
        (n + k * 5)).1) (Expression.eval env ((fbMux eb fixedTables ⟨k, hk⟩).output
        (n + k * 5)).2) hT
        = WeierstrassCurve.Projective.Point.toAffineLift
            (((4 + digitOf env eb k) * 4 ^ k) • Gpt) := by
      rw [hTval, hd]
      rfl
    rw [hval, hTval', add_assoc, ← toAffineLift_add, ← add_nsmul, ← winSum_succ]


/-! ## The fixed-base phase spec (plan §5) -/


/-! ## The fixed-base phase: operations and output split -/

/-- The operations of the fixed-base phase split into the initial shift addition
and the 128-window fold.  This is the per-phase equation lemma that lets parents
reason about the phase without ever unfolding the 128-iteration loop body. -/
theorem fixedBase_ops (h : Pt) (eb : Vector E 256) (n : Nat) :
    (fixedBase h eb).operations n
      = (affAdd h (cst shiftX, cst (-shiftY))).operations n
        ++ (Circuit.foldlRange 128 ((affAdd h (cst shiftX, cst (-shiftY))).output n)
              (fixedBaseBody eb fixedTables)
              (fixedBaseBody_constantLength eb fixedTables)).operations (n + 4) := by
  simp only [fixedBase, Circuit.operations, Circuit.output, affAdd_localLength]

/-- The output of the fixed-base phase is the output of the 128-window fold. -/
theorem fixedBase_out (h : Pt) (eb : Vector E 256) (n : Nat) :
    (fixedBase h eb).output n
      = (Circuit.foldlRange 128 ((affAdd h (cst shiftX, cst (-shiftY))).output n)
          (fixedBaseBody eb fixedTables)
          (fixedBaseBody_constantLength eb fixedTables)).output (n + 4) := by
  simp only [fixedBase, Circuit.operations, Circuit.output, affAdd_localLength]


/-! ## TEST -/
example (h : Pt) (eb : Vector E 256) (n : Nat) (env : Environment Fp)
    (hc : ConstraintsHold.Soundness env ((fixedBase h eb).operations n)) :
    ConstraintsHold.Soundness env ((affAdd h (cst shiftX, cst (-shiftY))).operations n
      ++ (Circuit.foldlRange 128 ((affAdd h (cst shiftX, cst (-shiftY))).output n)
            (fixedBaseBody eb fixedTables) (fixedBaseBody_constantLength eb fixedTables)).operations (n + 4)) :=
  hc


/-! ## Splitting soundness of an appended operation list -/

/-- The `ConstraintsHold.Soundness` condition, written as an explicit
`ConditionNoOffset`. -/
def soundnessCond (env : Environment Fp) : ConditionNoOffset Fp where
  assert e := env e = 0
  lookup l := l.Soundness env
  interact i := i.Guarantees env
  subcircuit s := s.Assumptions env → s.Spec env

/-- **Split the soundness of an appended operation list.**

Stated with the two halves as *explicit variables*: `Operations.forAllNoOffset_append`
then applies without `whnf`-ing either half.  If the halves are written out
inline, `whnf` reduces the left half to a concrete `cons` list and the append
structure is lost, which makes the unification loop. -/
theorem soundness_append (env : Environment Fp) (A B : Operations Fp)
    (h : ConstraintsHold.Soundness env (A ++ B)) :
    ConstraintsHold.Soundness env A ∧ B.forAllNoOffset (soundnessCond env) := by
  simp only [ConstraintsHold.Soundness, soundnessCond, Operations.forAllNoOffset_append] at h
  exact h


/-- **Per-step soundness of a `foldlRange`.**

The loop body's constraints at step `i` follow from the loop's constraints.
Stated with the loop parameters as variables so that
`Circuit.foldlRange.forAllNoOffset` applies without `whnf`-ing the fold. -/
theorem soundness_foldlRange (env : Environment Fp) {m : Nat} {β : Type} [Inhabited β]
    {init : β} {body : β → Fin m → Circuit Fp β}
    {constant : Circuit.ConstantLength fun (t : β × Fin m) => body t.1 t.2} {n : Nat}
    (h : ((Circuit.foldlRange m init body constant).operations n).forAllNoOffset
      (soundnessCond env)) :
    ∀ i : Fin m,
      ((body (Circuit.FoldlM.foldlAcc n (Vector.finRange m) body init i) i).operations
        (n + i * (body default i).localLength)).forAllNoOffset (soundnessCond env) := by
  rw [Circuit.foldlRange.forAllNoOffset] at h
  exact h


/-- **Split a phase into a prefix and a `foldlRange` loop, and expose the loop's
per-step constraints.**  The loop parameters are variables, so neither
`Operations.forAllNoOffset_append` nor `Circuit.foldlRange.forAllNoOffset` has to
`whnf` the fold. -/
theorem soundness_append_foldlRange (env : Environment Fp) (A : Operations Fp)
    {m : Nat} {β : Type} [Inhabited β] {init : β} {body : β → Fin m → Circuit Fp β}
    {constant : Circuit.ConstantLength fun (t : β × Fin m) => body t.1 t.2} {n : Nat}
    (h : ConstraintsHold.Soundness env
      (A ++ (Circuit.foldlRange m init body constant).operations n)) :
    ConstraintsHold.Soundness env A ∧
      ∀ i : Fin m,
        ((body (Circuit.FoldlM.foldlAcc n (Vector.finRange m) body init i) i).operations
          (n + i * (body default i).localLength)).forAllNoOffset (soundnessCond env) :=
  ⟨(soundness_append env A _ h).1, soundness_foldlRange env (soundness_append env A _ h).2⟩

/-- Generic invariant induction for `Fin.foldl`, with the step hypothesis stated
at the *actual* accumulator.

This is the form needed when the step's justification (here: the row
constraints of the loop body) is only available at the real accumulator, not at
an arbitrary one. -/
theorem fin_foldl_inv' {α : Type} {m : Nat} (f : α → Fin m → α) (init : α)
    (P : Nat → α → Prop) (h0 : P 0 init)
    (hstep : ∀ (j : Nat) (hj : j < m),
      P j (Fin.foldl j (fun acc (i : Fin j) => f acc ⟨i.val, by omega⟩) init) →
      P (j + 1) (f (Fin.foldl j (fun acc (i : Fin j) => f acc ⟨i.val, by omega⟩) init)
        ⟨j, hj⟩)) :
    ∀ (k : Nat) (hk : k ≤ m),
      P k (Fin.foldl k (fun acc (i : Fin k) => f acc ⟨i.val, by omega⟩) init) := by
  intro k
  induction k with
  | zero => intro _; simpa using h0
  | succ k ih =>
    intro hk
    rw [Fin.foldl_succ_last]
    exact hstep k (by omega) (ih (by omega))

/-! ## The fixed-base phase spec (plan §5) -/

set_option linter.constructorNameAsVariable false in
/-- **Fixed-base phase spec (plan §5).**

From *any* satisfying assignment of the phase's rows, the output is the affine
point `H + [E]G`, where `E = leNat eBit` is the digest read off the 256 Boolean
digest bits.  The only extra hypotheses are the Booleanity of the digest bits
and the distinct-`x` conditions of the 129 affine additions (the initial shift
addition and the 128 windows), which the global offset theorem supplies.

This is the group-level half of task T12; the row-level halves are
`affAdd_sound` (`Phases/TableSemantics.lean`) and `muxConst4W_tablePt`. -/
theorem fixedBase_spec (env : Environment Fp) (h : Pt) (eb : Vector E 256) (n : Nat)
    (hH : NS (Expression.eval env h.1) (Expression.eval env h.2))
    (hb : ∀ k : Fin 256,
      Expression.eval env (eb.get k) = 0 ∨ Expression.eval env (eb.get k) = 1)
    (hdx0 : Expression.eval env (cst shiftX) - Expression.eval env h.1 ≠ 0)
    (hdx : ∀ (k : Nat) (hk : k < 128),
      Expression.eval env ((fbMux eb fixedTables ⟨k, hk⟩).output (n + 4 + k * 5)).1
        - Expression.eval env (Circuit.FoldlM.foldlAcc (n + 4) (Vector.finRange 128)
            (fixedBaseBody eb fixedTables)
            ((affAdd h (cst shiftX, cst (-shiftY))).output n) ⟨k, hk⟩).1 ≠ 0)
    (hc : ConstraintsHold.Soundness env ((fixedBase h eb).operations n)) :
    ∃ hns : NS (Expression.eval env ((fixedBase h eb).output n).1)
        (Expression.eval env ((fixedBase h eb).output n).2),
      Affine.Point.some (Expression.eval env ((fixedBase h eb).output n).1)
        (Expression.eval env ((fixedBase h eb).output n).2) hns
        = Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH
          + WeierstrassCurve.Projective.Point.toAffineLift (digestNat env eb • Gpt) := by
  set Hpt : Affine.Point Wp :=
    Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH with hHpt
  -- the shift point is finite and is `shiftPt`
  have hS : NS shiftX shiftY :=
    ns_congr shiftX_eq shiftY_eq
      (affine_ns (mulG shiftNat) (mulG_on_curve shiftNat)
        (mulG_Z_ne_zero_gen shiftNat shiftNat_mod_ne_zero))
  have hshiftPt : Affine.Point.some shiftX shiftY hS = shiftPt :=
    (some_congr shiftX_eq shiftY_eq hS
      (affine_ns (mulG shiftNat) (mulG_on_curve shiftNat)
        (mulG_Z_ne_zero_gen shiftNat shiftNat_mod_ne_zero))).trans fixedShift_some
  have hB : NS (Expression.eval env (cst shiftX)) (Expression.eval env (cst (-shiftY))) :=
    negPt_ns hS
  have hneg : Affine.Point.some (Expression.eval env (cst shiftX))
      (Expression.eval env (cst (-shiftY))) hB = -shiftPt := by
    have h := negPt_group shiftX shiftY hS
    rw [hshiftPt] at h
    exact h
  -- split the phase into the initial addition and the 128-window fold
  have hc' : ConstraintsHold.Soundness env
      ((affAdd h (cst shiftX, cst (-shiftY))).operations n
        ++ (Circuit.foldlRange 128 ((affAdd h (cst shiftX, cst (-shiftY))).output n)
              (fixedBaseBody eb fixedTables)
              (fixedBaseBody_constantLength eb fixedTables)).operations (n + 4)) := hc
  obtain ⟨hc1, hc2⟩ := soundness_append_foldlRange env
    ((affAdd h (cst shiftX, cst (-shiftY))).operations n) hc'
  -- the initial addition
  have hout0 : (affAdd h (cst shiftX, cst (-shiftY))).output n
      = (Expression.var (F := Fp) ⟨n + 2⟩, Expression.var (F := Fp) ⟨n + 3⟩) := by
    simp only [affAdd_output]
  have hcl : ∀ (i : Fin 128),
      (fixedBaseBody eb fixedTables default i).localLength = 5 := fun i =>
    (fixedBaseBody_constantLength eb fixedTables).localLength_eq (default, i) 0
  have hinit : fbInv env eb Hpt 0 ((affAdd h (cst shiftX, cst (-shiftY))).output n) := by
    rw [hout0]
    obtain ⟨hR0, hR0val⟩ :=
      affAdd_sound env h (cst shiftX, cst (-shiftY)) n hH hB hdx0 hc1
    refine ⟨hR0, hR0val.trans ?_⟩
    rw [hneg]
    simp only [hHpt, winSum, Finset.range_zero, Finset.sum_empty, zero_nsmul,
      toAffineLift_zero, add_zero]
  -- one window preserves the invariant
  have hstep : ∀ (j : Nat) (hj : j < 128),
      fbInv env eb Hpt j (Fin.foldl j (fun acc (i : Fin j) =>
        (fixedBaseBody eb fixedTables acc ⟨i.val, by omega⟩).output (n + 4 + i.val * 5))
        ((affAdd h (cst shiftX, cst (-shiftY))).output n)) →
      fbInv env eb Hpt (j + 1) ((fixedBaseBody eb fixedTables
        (Fin.foldl j (fun acc (i : Fin j) =>
          (fixedBaseBody eb fixedTables acc ⟨i.val, by omega⟩).output (n + 4 + i.val * 5))
          ((affAdd h (cst shiftX, cst (-shiftY))).output n)) ⟨j, hj⟩).output
        (n + 4 + j * 5)) := by
    intro j hj hacc
    have hcj := hc2 ⟨j, hj⟩
    rw [hcl ⟨j, hj⟩] at hcj
    rw [foldlAcc_eq env eb fixedTables ((affAdd h (cst shiftX, cst (-shiftY))).output n)
      (n + 4) j hj] at hcj
    have hdxj := hdx j hj
    rw [foldlAcc_eq env eb fixedTables ((affAdd h (cst shiftX, cst (-shiftY))).output n)
      (n + 4) j hj] at hdxj
    exact fbStep env eb Hpt (n + 4) j hj _ (hb ⟨2 * j, by omega⟩)
      (hb ⟨2 * j + 1, by omega⟩) hdxj hacc hcj
  -- run the induction
  have hP := fin_foldl_inv' (fun acc (i : Fin 128) =>
      (fixedBaseBody eb fixedTables acc i).output (n + 4 + i.val * 5))
    ((affAdd h (cst shiftX, cst (-shiftY))).output n)
    (fun k acc => fbInv env eb Hpt k acc) hinit hstep 128 (by omega)
  -- identify the fold output with the phase output
  have hfold : (Circuit.foldlRange 128 ((affAdd h (cst shiftX, cst (-shiftY))).output n)
        (fixedBaseBody eb fixedTables)
        (fixedBaseBody_constantLength eb fixedTables)).output (n + 4)
      = Fin.foldl 128 (fun acc (i : Fin 128) =>
          (fixedBaseBody eb fixedTables acc ⟨i.val, by omega⟩).output (n + 4 + i.val * 5))
          ((affAdd h (cst shiftX, cst (-shiftY))).output n) := by
    rw [Circuit.foldlRange.output_eq]
    simp only [hcl]
  have houtEq : (fixedBase h eb).output n
      = Fin.foldl 128 (fun acc (i : Fin 128) =>
          (fixedBaseBody eb fixedTables acc ⟨i.val, by omega⟩).output (n + 4 + i.val * 5))
          ((affAdd h (cst shiftX, cst (-shiftY))).output n) :=
    (fixedBase_out h eb n).trans hfold
  obtain ⟨hns, hval⟩ := hP
  rw [houtEq]
  refine ⟨hns, hval.trans ?_⟩
  rw [winSum_128, add_nsmul, toAffineLift_add]
  simp only [shiftPt]
  abel

end StandardECDSA.Phases
