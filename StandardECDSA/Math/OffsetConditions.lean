/-
# Offset conditions: the bad-equation family

The alternating-offset design chooses a nonzero offset `H = [k]G` so that every
affine addition/doubling performed by the circuit has a nonzero denominator.
Each failure is an equation `[a]H = B` with `a ∈ {±1, ±2, ±3, ±4}` and `B`
independent of `H`; the plan enumerates 1,039 such slots.

This module provides

* the generic ELM algebra identities (sign cancellation, collision
  characterisations) in an arbitrary abelian group;
* the generic finite-exception counting theorem
  `exists_avoiding_injective_equations`;
* the P-256 geometric fact that two finite on-curve points with the same affine
  `x`-coordinate are equal or negatives — the bridge from "denominator zero" to
  "one of the listed equations";
* the `GoodOffset` predicate, defined from group points and required distinct-`x`
  conditions, never from constraint satisfaction.

The *enumeration* of the 1,039 slots and the coverage theorem
"every failure of admissibility implies one listed equation" is task T13 and is
blocked on the circuit phases of T12/T15: the slots are indexed by the actual
affine operations of the implementation, which do not exist yet.  Nothing here
assumes that enumeration.
-/

import StandardECDSA.Math.GroupOrder

namespace StandardECDSA.Math

open StandardECDSA

set_option maxRecDepth 100000

/-! ## Generic ELM algebra -/

section ElmAlgebra

variable {A : Type} [AddCommGroup A]

/-- One ELM step with signed offset `q = σ·H` preserves the ladder invariant. -/
theorem elm_offset_step_invariant (c q t : A) :
    2 • (c + q) + (t - 3 • q) = (2 • c + t) - q := by abel

/-- The first ELM addition has equal inputs iff `4q = t - c`. -/
theorem elm_first_same_collision (c q t : A) :
    c + q = t - 3 • q ↔ 4 • q = t - c := by
  constructor
  · intro heq
    calc 4 • q = (t - c) + ((c + q) - (t - 3 • q)) := by abel
      _ = t - c := by rw [heq, sub_self, add_zero]
  · intro heq
    calc c + q = (t - 3 • q) + (4 • q - (t - c)) := by abel
      _ = t - 3 • q := by rw [heq, sub_self, add_zero]

/-- The first ELM addition has opposite inputs iff `2q = c + t`. -/
theorem elm_first_opposite_collision (c q t : A) :
    c + q = -(t - 3 • q) ↔ 2 • q = c + t := by
  constructor
  · intro heq
    calc 2 • q = (c + t) + (-(t - 3 • q) - (c + q)) := by abel
      _ = c + t := by rw [heq, sub_self, add_zero]
  · intro heq
    calc c + q = -(t - 3 • q) + ((c + t) - 2 • q) := by abel
      _ = -(t - 3 • q) := by rw [heq, sub_self, add_zero]

/-- The second ELM addition has equal inputs only in the degenerate case `b = 0`. -/
theorem elm_second_same_collision (a b : A) : a + b = a ↔ b = 0 := by
  constructor
  · intro h
    have := congr_arg (fun z => z - a) h
    simpa using this
  · rintro rfl; abel

/-- The second ELM addition has opposite inputs iff `2a + b = 0`. -/
theorem elm_second_opposite_collision (a b : A) : a + b = -a ↔ 2 • a + b = 0 := by
  constructor
  · intro heq
    calc 2 • a + b = a + (a + b) := by abel
      _ = 0 := by rw [heq]; abel
  · intro heq
    calc a + b = -a + (2 • a + b) := by abel
      _ = -a := by rw [heq, add_zero]

end ElmAlgebra

/-! ## Finite-exception counting -/

/-- Each injective equation `f i c = target i` excludes at most one candidate, so
`m` equations cannot exhaust a candidate set of more than `m` elements. -/
theorem exists_avoiding_injective_equations
    {C A : Type} [Fintype C] {m : Nat}
    (f : Fin m → C → A) (hf : ∀ i, Function.Injective (f i))
    (target : Fin m → A) (hcard : m < Fintype.card C) :
    ∃ c, ∀ i, f i c ≠ target i := by
  classical
  let bad (i : Fin m) : Finset C := Finset.univ.filter (fun c => f i c = target i)
  have hi : ∀ i, (bad i).card ≤ 1 := by
    intro i
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact hf i ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  have hb : (Finset.univ.biUnion bad).card ≤ m := by
    calc _ ≤ ∑ i : Fin m, (bad i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin m, 1 := Finset.sum_le_sum (fun i _ => hi i)
      _ = m := by simp
  have hex : ∃ c, c ∉ Finset.univ.biUnion bad := by
    by_contra hh
    push_neg at hh
    have heq : Finset.univ.biUnion bad = Finset.univ := Finset.eq_univ_of_forall hh
    rw [heq, Finset.card_univ] at hb
    omega
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, ?_⟩
  intro i heq
  exact hc (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩⟩)

/-! ## Same-`x` implies equal or negative -/

/-- Two affine on-curve P-256 points with the same `x`-coordinate are equal or
negatives.  This is the bridge from "an addition denominator vanishes" to "one
of the listed bad equations holds". -/
theorem same_x_eq_or_neg {x y₁ y₂ : K}
    (h₁ : WeierstrassCurve.Affine.Equation params.toMathlib x y₁)
    (h₂ : WeierstrassCurve.Affine.Equation params.toMathlib x y₂) :
    y₁ = y₂ ∨ y₁ = -y₂ :=
  y_eq_or_neg h₁ h₂

/-! ## The admissibility predicate -/

/-- A finite family of bad equations `[c]H = B` with `0 < c < n` that a good
offset must avoid.  Negative coefficients are absorbed into the target, since
`[-c]H = B ↔ [c]H = -B`. -/
structure BadFamily (A : Type) where
  /-- The number of bad equations. -/
  m : Nat
  /-- The (positive) coefficient `c` of each equation. -/
  coeff : Fin m → Nat
  /-- Each coefficient is positive. -/
  coeff_pos : ∀ i, 0 < coeff i
  /-- Each coefficient is below the group order. -/
  coeff_lt : ∀ i, coeff i < n
  /-- The right-hand side `B` of each equation. -/
  target : Fin m → A

/-- `H` avoids every equation of the family. -/
def BadFamily.Avoids {A : Type} [AddCommGroup A] (fam : BadFamily A) (H : A) : Prop :=
  ∀ i, (fam.coeff i) • H ≠ fam.target i

/-- Geometric admissibility of an offset `H` for the given signature data.

`H` must be a finite on-curve point, and it must avoid the bad-equation family
generated by the actual affine operations of the circuit.  The family is a
parameter: the plan's 1,039 slots are its instantiation for the concrete
implementation (task T13), which is blocked on the circuit phases.
-/
def GoodOffset (H : AffinePoint K) (hH : H.IsOnCurve params)
    (fam : BadFamily (params.toMathlib).toProjective.Point) : Prop :=
  (H.toProjective).Z ≠ 0 ∧
  fam.Avoids (H.toProjective.toMathlibPoint params
    (affine_to_projective_on_curve H params hH))

/-- The generic existence statement: a family of `m` injective bad equations
cannot exhaust a candidate set of more than `m` points.  Instantiating this with
the 1,039 slots and the 1,040 candidates `[k]G` is task T14. -/
theorem exists_avoiding_of_injective
    {C : Type} [Fintype C]
    (fam : BadFamily (params.toMathlib).toProjective.Point)
    (f : C → (params.toMathlib).toProjective.Point) (hf : Function.Injective f)
    (hcard : fam.m < Fintype.card C) :
    ∃ c, fam.Avoids (f c) := by
  classical
  have h := exists_avoiding_injective_equations
    (fun i c => (fam.coeff i) • f c)
    (fun i => (nsmul_injective_of_lt (fam.coeff i) (fam.coeff_pos i) (fam.coeff_lt i)).comp hf)
    fam.target hcard
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc⟩

end StandardECDSA.Math
