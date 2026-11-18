/-
# Single-row R1CS certificates for the standard circuit's gadgets

Every assertion in the standard circuit has the shape

```text
A * B - C
```

with `A`, `B`, `C` affine (`degree ≤ 1`), possibly with further affine summands
subtracted.  `Challenge.CostR1CS.r1csProducts` counts the genuine quadratic
products along the `add` spine; this file proves that such expressions report
`some 1` (or `some 0` when a factor is constant), hence are single R1CS rows,
and lifts the result to `IsR1CSCirc` for each gadget.

Task T05-T11 (structural half).
-/

import StandardECDSA.Gadgets.Cost

namespace StandardECDSA.Gadgets

open Challenge.CostR1CS

/-! ## `r1csProducts` on affine expressions -/

/-- An affine expression contains no genuine product. -/
theorem r1csProducts_affine {e : E} (h : deg e ≤ 1) : r1csProducts e = some 0 := by
  induction e with
  | const c => rfl
  | var v => rfl
  | add a b iha ihb =>
      have ha : deg a ≤ 1 := by
        have : max (deg a) (deg b) ≤ 1 := h
        omega
      have hb : deg b ≤ 1 := by
        have : max (deg a) (deg b) ≤ 1 := h
        omega
      show (match r1csProducts a, r1csProducts b with
        | some m, some n => some (m + n)
        | _, _ => none) = some 0
      rw [iha ha, ihb hb]
  | mul a b iha ihb =>
      have hd : deg a + deg b ≤ 1 := h
      by_cases h0 : deg a = 0
      · have hb : deg b ≤ 1 := by omega
        show (if deg a = 0 then r1csProducts b
          else if deg b = 0 then r1csProducts a
          else if deg a ≤ 1 ∧ deg b ≤ 1 then some 1 else none) = some 0
        rw [if_pos h0]
        exact ihb hb
      · have hb0 : deg b = 0 := by omega
        show (if deg a = 0 then r1csProducts b
          else if deg b = 0 then r1csProducts a
          else if deg a ≤ 1 ∧ deg b ≤ 1 then some 1 else none) = some 0
        rw [if_neg h0, if_pos hb0]
        exact iha (by omega)

/-- A product of two affine expressions is at most one R1CS product. -/
theorem r1csProducts_mul_le_one {a b : E} (ha : deg a ≤ 1) (hb : deg b ≤ 1) :
    ∃ k, r1csProducts (Expression.mul a b) = some k ∧ k ≤ 1 := by
  by_cases h0 : deg a = 0
  · exact ⟨0, by
      show (if deg a = 0 then r1csProducts b
        else if deg b = 0 then r1csProducts a
        else if deg a ≤ 1 ∧ deg b ≤ 1 then some 1 else none) = some 0
      rw [if_pos h0]; exact r1csProducts_affine hb, by omega⟩
  · by_cases h1 : deg b = 0
    · exact ⟨0, by
        show (if deg a = 0 then r1csProducts b
          else if deg b = 0 then r1csProducts a
          else if deg a ≤ 1 ∧ deg b ≤ 1 then some 1 else none) = some 0
        rw [if_neg h0, if_pos h1]; exact r1csProducts_affine ha, by omega⟩
    · exact ⟨1, by
        show (if deg a = 0 then r1csProducts b
          else if deg b = 0 then r1csProducts a
          else if deg a ≤ 1 ∧ deg b ≤ 1 then some 1 else none) = some 1
        rw [if_neg h0, if_neg h1, if_pos ⟨ha, hb⟩], by omega⟩

/-- `r1csProducts` is additive over `add`. -/
theorem r1csProducts_add {a b : E} {m n : Nat}
    (ha : r1csProducts a = some m) (hb : r1csProducts b = some n) :
    r1csProducts (Expression.add a b) = some (m + n) := by
  show (match r1csProducts a, r1csProducts b with
    | some m, some n => some (m + n)
    | _, _ => none) = some (m + n)
  rw [ha, hb]

/-- Multiplying by a constant does not change the product count. -/
theorem r1csProducts_mul_const (c : Fp) {e : E} {n : Nat} (h : r1csProducts e = some n) :
    r1csProducts (Expression.mul (Expression.const c) e) = some n := by
  show (if deg (Expression.const c) = 0 then r1csProducts e
    else if deg e = 0 then r1csProducts (Expression.const c)
    else if deg (Expression.const c) ≤ 1 ∧ deg e ≤ 1 then some 1 else none) = some n
  rw [if_pos (show deg (Expression.const c) = 0 from rfl)]
  exact h

/-- Negation preserves affineness. -/
theorem deg_neg_le {e : E} (h : deg e ≤ 1) : deg (-e) ≤ 1 := by
  show 0 + deg e ≤ 1
  omega

/-! ## Row shapes -/

/-- An affine expression is a single R1CS row. -/
theorem isR1CSRow_affine {e : E} (h : deg e ≤ 1) : isR1CSRow e := by
  unfold isR1CSRow
  rw [r1csProducts_affine h]
  decide

/-- `A * B - C` with `A`, `B`, `C` affine is a single R1CS row. -/
theorem isR1CSRow_prod_sub {A B C : E} (hA : deg A ≤ 1) (hB : deg B ≤ 1) (hC : deg C ≤ 1) :
    isR1CSRow (pm A B - C) := by
  obtain ⟨k, hk, hk1⟩ := r1csProducts_mul_le_one hA hB
  have hC0 : r1csProducts C = some 0 := r1csProducts_affine hC
  have hneg : r1csProducts (Expression.mul (Expression.const (-1)) C) = some 0 :=
    r1csProducts_mul_const (-1) hC0
  unfold isR1CSRow pm
  show (match r1csProducts (Expression.add (Expression.mul A B)
    (Expression.mul (Expression.const (-1)) C)) with
    | some k => k ≤ 1
    | none => False)
  rw [r1csProducts_add hk hneg]
  show k + 0 ≤ 1
  omega

/-- Adding an affine summand to a single R1CS row keeps it a single row. -/
theorem isR1CSRow_add_affine {a c : E} (ha : isR1CSRow a) (hc : deg c ≤ 1) :
    isR1CSRow (Expression.add a c) := by
  have hc0 : r1csProducts c = some 0 := r1csProducts_affine hc
  unfold isR1CSRow at *
  cases h : r1csProducts a with
  | none => rw [h] at ha; exact ha.elim
  | some k =>
      rw [h] at ha
      rw [r1csProducts_add h hc0]
      simpa using ha

/-- `A * B - C - D` with all four affine is a single R1CS row. -/
theorem isR1CSRow_prod_sub2 {A B C D : E} (hA : deg A ≤ 1) (hB : deg B ≤ 1)
    (hC : deg C ≤ 1) (hD : deg D ≤ 1) :
    isR1CSRow (pm A B - C - D) :=
  isR1CSRow_add_affine (isR1CSRow_prod_sub hA hB hC) (deg_neg_le hD)

/-- `A * B - C - D - F` with all five affine is a single R1CS row. -/
theorem isR1CSRow_prod_sub3 {A B C D F : E} (hA : deg A ≤ 1) (hB : deg B ≤ 1)
    (hC : deg C ≤ 1) (hD : deg D ≤ 1) (hF : deg F ≤ 1) :
    isR1CSRow (pm A B - C - D - F) :=
  isR1CSRow_add_affine (isR1CSRow_prod_sub2 hA hB hC hD) (deg_neg_le hF)

/-! ## `mat` and the leaf gadgets -/

/-- `matDeg` is at most one. -/
theorem matDeg_le_one (e : E) : matDeg e ≤ 1 := by
  rw [matDeg_eq_min]
  omega

/-- `mat` is a single-row R1CS circuit. -/
theorem isR1CSCirc_mat (e : E) : IsR1CSCirc (mat e) := by
  induction e with
  | var v => exact IsR1CSCirc.pure _
  | const c => exact IsR1CSCirc.pure _
  | add a b iha ihb =>
      unfold mat
      refine IsR1CSCirc.bind_out iha (fun n => ?_)
      refine IsR1CSCirc.bind_out ihb (fun n' => ?_)
      exact IsR1CSCirc.pure _
  | mul a b iha ihb =>
      unfold mat
      refine IsR1CSCirc.bind_out iha (fun n => ?_)
      refine IsR1CSCirc.bind_out ihb (fun n' => ?_)
      by_cases h : deg a = 0 ∨ deg b = 0
      · rw [if_pos h]
        exact IsR1CSCirc.pure _
      · rw [if_neg h]
        refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) (fun n'' => ?_)
        refine IsR1CSCirc.bind_out (IsR1CSCirc.assertZero ?_) (fun _ => IsR1CSCirc.pure _)
        exact isR1CSRow_prod_sub
          (by rw [(mat_spec a).2 n]; exact matDeg_le_one a)
          (by rw [(mat_spec b).2 n']; exact matDeg_le_one b)
          (by show deg (Expression.var ⟨n''⟩) ≤ 1; simp [deg])

/-- `assertBool` is a single R1CS row. -/
theorem isR1CSCirc_assertBool (b : E) (hb : deg b ≤ 1) : IsR1CSCirc (assertBool b) := by
  unfold assertBool
  exact IsR1CSCirc.assertZero (isR1CSRow_prod_sub hb hb hb)

/-- `nonzero` is a single R1CS row. -/
theorem isR1CSCirc_nonzero (x : E) (hx : deg x ≤ 1) : IsR1CSCirc (nonzero x) := by
  unfold nonzero
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) (fun n => ?_)
  refine IsR1CSCirc.bind_out (IsR1CSCirc.assertZero ?_) (fun _ => IsR1CSCirc.pure _)
  exact isR1CSRow_prod_sub hx
    (by show deg (Expression.var ⟨n⟩) ≤ 1; simp [deg])
    (by show deg (Expression.const (1 : Fp)) ≤ 1; simp [deg])

/-- `sel` is a single-row R1CS circuit. -/
theorem isR1CSCirc_sel (b x0 x1 : E) : IsR1CSCirc (sel b x0 x1) := by
  unfold sel
  exact isR1CSCirc_mat _

/-- `muxConst4` is a single-row R1CS circuit. -/
theorem isR1CSCirc_muxConst4 (b0 b1 : E) (tab : Array (Fp × Fp)) :
    IsR1CSCirc (muxConst4 b0 b1 tab) := by
  unfold muxConst4
  refine IsR1CSCirc.bind_out (isR1CSCirc_mat _) (fun n => ?_)
  exact IsR1CSCirc.pure _

/-- `mux4` is a single-row R1CS circuit. -/
theorem isR1CSCirc_mux4 (b0 b1 : E) (p0 p1 p2 p3 : Pt) :
    IsR1CSCirc (mux4 b0 b1 p0 p1 p2 p3) := by
  unfold mux4
  refine IsR1CSCirc.bind_out (isR1CSCirc_sel _ _ _) (fun n => ?_)
  refine IsR1CSCirc.bind_out (isR1CSCirc_sel _ _ _) (fun n => ?_)
  refine IsR1CSCirc.bind_out (isR1CSCirc_sel _ _ _) (fun n => ?_)
  refine IsR1CSCirc.bind_out (isR1CSCirc_sel _ _ _) (fun n => ?_)
  refine IsR1CSCirc.bind_out (isR1CSCirc_sel _ _ _) (fun n => ?_)
  refine IsR1CSCirc.bind_out (isR1CSCirc_sel _ _ _) (fun n => ?_)
  exact IsR1CSCirc.pure _

/-- A wire variable is affine. -/
theorem deg_var_le (n : Nat) : deg (Expression.var (F := Fp) ⟨n⟩) ≤ 1 := by
  show 1 ≤ 1
  omega

/-- `affAdd` is a single-row R1CS circuit. -/
theorem isR1CSCirc_affAdd (p q : Pt)
    (hp : deg p.1 ≤ 1 ∧ deg p.2 ≤ 1) (hq : deg q.1 ≤ 1 ∧ deg q.2 ≤ 1) :
    IsR1CSCirc (affAdd p q) := by
  have hdx : deg (q.1 - p.1) ≤ 1 := by
    rw [show deg (q.1 - p.1) = max (deg q.1) (deg p.1) from
      Challenge.CostR1CS.degree_sub q.1 p.1]
    exact Nat.max_le.2 ⟨hq.1, hp.1⟩
  have hdy : deg (q.2 - p.2) ≤ 1 := by
    rw [show deg (q.2 - p.2) = max (deg q.2) (deg p.2) from
      Challenge.CostR1CS.degree_sub q.2 p.2]
    exact Nat.max_le.2 ⟨hq.2, hp.2⟩
  unfold affAdd
  refine IsR1CSCirc.bind_out (isR1CSCirc_nonzero _ hdx) (fun n => ?_)
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) (fun n1 => ?_)
  refine IsR1CSCirc.bind_out (IsR1CSCirc.assertZero ?_) (fun _ => ?_)
  · exact isR1CSRow_prod_sub hdx (deg_var_le n1) hdy
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) (fun n2 => ?_)
  refine IsR1CSCirc.bind_out (IsR1CSCirc.assertZero ?_) (fun _ => ?_)
  · exact isR1CSRow_prod_sub3 (deg_var_le n1) (deg_var_le n1) hp.1 hq.1 (deg_var_le n2)
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) (fun n3 => ?_)
  have hsub : deg (p.1 - (Expression.var ⟨n2⟩ : E)) ≤ 1 := by
    rw [show deg (p.1 - (Expression.var ⟨n2⟩ : E)) =
      max (deg p.1) (deg (Expression.var ⟨n2⟩ : E)) from
      Challenge.CostR1CS.degree_sub p.1 _]
    exact Nat.max_le.2 ⟨hp.1, deg_var_le n2⟩
  refine IsR1CSCirc.bind_out (IsR1CSCirc.assertZero ?_) (fun _ => ?_)
  · exact isR1CSRow_prod_sub2 (deg_var_le n1) hsub hp.2 (deg_var_le n3)
  exact IsR1CSCirc.pure _

/-- `affDouble` is a single-row R1CS circuit. -/
theorem isR1CSCirc_affDouble (p : Pt) (hp : deg p.1 ≤ 1 ∧ deg p.2 ≤ 1) :
    IsR1CSCirc (affDouble p) := by
  unfold affDouble
  refine IsR1CSCirc.bind_out (isR1CSCirc_mat _) (fun n => ?_)
  have hxx : deg (Circuit.output (mm p.1 p.1) n) ≤ 1 := by
    show deg (Circuit.output (mat (Expression.mul p.1 p.1)) n) ≤ 1
    rw [(mat_spec (Expression.mul p.1 p.1)).2 n]
    exact matDeg_le_one _
  have h2y : deg (sc 2 p.2) ≤ 1 := by
    show 0 + deg p.2 ≤ 1
    exact Nat.zero_add _ ▸ hp.2
  have h3x : deg (sc 3 (Circuit.output (mm p.1 p.1) n)) ≤ 1 := by
    show 0 + deg (Circuit.output (mm p.1 p.1) n) ≤ 1
    exact Nat.zero_add _ ▸ hxx
  have h2x : deg (sc 2 p.1) ≤ 1 := by
    show 0 + deg p.1 ≤ 1
    exact Nat.zero_add _ ▸ hp.1
  have hpa : deg (cst pa) ≤ 1 := by
    show (0 : Nat) ≤ 1
    exact Nat.zero_le 1
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) (fun n1 => ?_)
  refine IsR1CSCirc.bind_out (IsR1CSCirc.assertZero ?_) (fun _ => ?_)
  · exact isR1CSRow_prod_sub2 h2y (deg_var_le n1) h3x hpa
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) (fun n2 => ?_)
  refine IsR1CSCirc.bind_out (IsR1CSCirc.assertZero ?_) (fun _ => ?_)
  · exact isR1CSRow_prod_sub2 (deg_var_le n1) (deg_var_le n1) h2x (deg_var_le n2)
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) (fun n3 => ?_)
  have hsub : deg (p.1 - (Expression.var ⟨n2⟩ : E)) ≤ 1 := by
    rw [show deg (p.1 - (Expression.var ⟨n2⟩ : E)) =
      max (deg p.1) (deg (Expression.var ⟨n2⟩ : E)) from
      Challenge.CostR1CS.degree_sub p.1 _]
    exact Nat.max_le.2 ⟨hp.1, deg_var_le n2⟩
  refine IsR1CSCirc.bind_out (IsR1CSCirc.assertZero ?_) (fun _ => ?_)
  · exact isR1CSRow_prod_sub2 (deg_var_le n1) hsub hp.2 (deg_var_le n3)
  exact IsR1CSCirc.pure _

/-! ## Scalar comparators -/

/-- Folding affine summands keeps the accumulator affine. -/
theorem foldl_add_deg (l : List Nat) (f : Nat → E) (hf : ∀ j, deg (f j) ≤ 1)
    {m : E} (hm : deg m ≤ 1) : deg (l.foldl (fun m j => m + f j) m) ≤ 1 := by
  induction l generalizing m with
  | nil => exact hm
  | cons j js ih =>
      exact ih (m := m + f j) (by
        rw [show deg (m + f j) = max (deg m) (deg (f j)) from rfl]
        exact Nat.max_le.2 ⟨hm, hf j⟩)

theorem addMissing_deg (a : Nat → E) (ha : ∀ i, deg (a i) ≤ 1) (hi lo : Nat)
    {m : E} (hm : deg m ≤ 1) : deg (addMissing a hi lo m) ≤ 1 := by
  unfold addMissing
  refine foldl_add_deg _ _ (fun j => ?_) hm
  rw [show deg (cst 1 - a (hi - j)) = max (deg (cst 1)) (deg (a (hi - j))) from
    Challenge.CostR1CS.degree_sub _ _]
  exact Nat.max_le.2 ⟨by show (0 : Nat) ≤ 1; exact Nat.zero_le 1, ha _⟩

theorem runSum_deg (a : Nat → E) (ha : ∀ i, deg (a i) ≤ 1) (hi lo : Nat) :
    deg (runSum a hi lo) ≤ 1 := by
  unfold runSum
  refine foldl_add_deg _ _ (fun j => ha _) ?_
  show (0 : Nat) ≤ 1
  exact Nat.zero_le 1

/-- The comparison loop is a single-row R1CS circuit. -/
theorem isR1CSCirc_ltLoop (a : Nat → E) (ha : ∀ i, deg (a i) ≤ 1) (missing : E)
    (hm : deg missing ≤ 1) (l : List (Nat × Nat × Bool)) :
    IsR1CSCirc (ltLoop a missing l) := by
  induction l generalizing missing with
  | nil => exact IsR1CSCirc.pure ()
  | cons it rest ih =>
      obtain ⟨hi, lo, bit⟩ := it
      unfold ltLoop
      by_cases hb : bit
      · rw [if_pos hb]
        exact ih _ (addMissing_deg a ha hi lo hm)
      · rw [if_neg hb]
        refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) (fun n => ?_)
        refine IsR1CSCirc.bind_out (IsR1CSCirc.assertZero ?_) (fun _ => ?_)
        · exact isR1CSRow_prod_sub hm (deg_var_le n) (runSum_deg a ha hi lo)
        exact ih _ hm

/-- The guarded comparison loop is a single-row R1CS circuit. -/
theorem isR1CSCirc_ltLoopGuarded (a : Nat → E) (ha : ∀ i, deg (a i) ≤ 1)
    (guard missing : E) (hg : deg guard ≤ 1) (hm : deg missing ≤ 1)
    (l : List (Nat × Nat × Bool)) :
    IsR1CSCirc (ltLoopGuarded a guard missing l) := by
  induction l generalizing missing with
  | nil => exact IsR1CSCirc.pure ()
  | cons it rest ih =>
      obtain ⟨hi, lo, bit⟩ := it
      unfold ltLoopGuarded
      by_cases hb : bit
      · rw [if_pos hb]
        exact ih _ (addMissing_deg a ha hi lo hm)
      · rw [if_neg hb]
        refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) (fun n => ?_)
        refine IsR1CSCirc.bind_out (IsR1CSCirc.assertZero ?_) (fun _ => ?_)
        · refine isR1CSRow_prod_sub ?_ (deg_var_le n) (runSum_deg a ha hi lo)
          rw [show deg (missing + (cst 1 - guard)) =
            max (deg missing) (deg (cst 1 - guard)) from rfl]
          refine Nat.max_le.2 ⟨hm, ?_⟩
          rw [show deg (cst 1 - guard) = max (deg (cst 1)) (deg guard) from
            Challenge.CostR1CS.degree_sub _ _]
          exact Nat.max_le.2 ⟨by show (0 : Nat) ≤ 1; exact Nat.zero_le 1, hg⟩
        exact ih _ hm

/-- `assertLtOrderOf` is a single-row R1CS circuit. -/
theorem isR1CSCirc_assertLtOrderOf (bound : Nat) (a : Nat → E)
    (ha : ∀ i, deg (a i) ≤ 1) : IsR1CSCirc (assertLtOrderOf bound a) :=
  isR1CSCirc_ltLoop a ha (cst 0) (by show (0 : Nat) ≤ 1; exact Nat.zero_le 1) _

/-- `assertLtOrderGuardedOf` is a single-row R1CS circuit. -/
theorem isR1CSCirc_assertLtOrderGuardedOf (bound : Nat) (guard : E) (a : Nat → E)
    (ha : ∀ i, deg (a i) ≤ 1) (hg : deg guard ≤ 1) :
    IsR1CSCirc (assertLtOrderGuardedOf bound guard a) :=
  isR1CSCirc_ltLoopGuarded a ha guard (cst 0) hg
    (by show (0 : Nat) ≤ 1; exact Nat.zero_le 1) _

end StandardECDSA.Gadgets
