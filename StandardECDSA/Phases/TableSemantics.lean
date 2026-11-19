/-
# Row-level group semantics of the affine gadgets at arbitrary offsets

`Gadgets/Semantics3.lean` proves `affAddMain_soundness` / `affDoubleMain_soundness`
for the *bundled* `FormalCircuit` interface, where the input is a `fields 4`
variable and the offset is `i₀`.  The phases call `affAdd` / `affDouble`
directly on arbitrary expressions at arbitrary offsets, so they need the same
content in offset-generic form.

This module supplies that, plus the group semantics of `negPt`, and then
composes them into the shifted-table contract of plan §3A.

Task T12 (table half).
-/

import StandardECDSA.Gadgets.Semantics3
import StandardECDSA.Gadgets.LocalLength
import StandardECDSA.Phases.ShiftedTables

namespace StandardECDSA.Phases

open StandardECDSA.Gadgets
open WeierstrassCurve

/-- The operations of `shiftedTables` are the second component of its run.

Stated with opaque arguments so that the `rfl` proof never unfolds the
`do`-notation bind chain; parents use it to convert a `Soundness` hypothesis
about `(shiftedTables h q r n).2` into one about `(shiftedTables h q r).operations n`
without a definitional-unfolding check. -/
theorem shiftedTables_snd (h q r : Pt) (n : Nat) :
    (shiftedTables h q r n).2 = (shiftedTables h q r).operations n := rfl

/-! ## Offset-generic row-level soundness -/

/-- `sc c e` evaluates to `c` times the value of `e`. -/
theorem eval_sc (env : Environment Fp) (c : Fp) (e : E) :
    Expression.eval env (sc c e) = c * Expression.eval env e := rfl

/-- The four rows of `affAdd p q` at offset `n` give the group sum of `p` and
`q`, with the output at `n + 2`, `n + 3`. -/
theorem affAdd_sound (env : Environment Fp) (p q : Pt) (n : Nat)
    (hA : NS (Expression.eval env p.1) (Expression.eval env p.2))
    (hB : NS (Expression.eval env q.1) (Expression.eval env q.2))
    (hDx : Expression.eval env q.1 - Expression.eval env p.1 ≠ 0)
    (h : ConstraintsHold.Soundness env ((affAdd p q).operations n)) :
    ∃ hR : NS (env.get (n + 2)) (env.get (n + 3)),
      Affine.Point.some (env.get (n + 2)) (env.get (n + 3)) hR
        = Affine.Point.some (Expression.eval env p.1) (Expression.eval env p.2) hA
          + Affine.Point.some (Expression.eval env q.1) (Expression.eval env q.2) hB := by
  simp only [affAdd, nonzero, circuit_norm, pm] at h
  obtain ⟨r1, r2, r3, r4⟩ := h
  rw [show n + 1 + 1 = n + 2 from by omega] at r3
  rw [show n + 1 + 1 = n + 2 from by omega,
      show n + 1 + 1 + 1 = n + 3 from by omega] at r4
  refine affAddEqs_group #v[Expression.eval env p.1, Expression.eval env p.2,
    Expression.eval env q.1, Expression.eval env q.2] (env.get (n + 2), env.get (n + 3))
    hA hB hDx ⟨env.get (n + 1), ?_, ?_, ?_⟩
  · exact sub_eq_zero.mp r2
  · exact (sub_eq_zero.mp r3).symm
  · exact (sub_eq_zero.mp r4).symm

/-- The inverse row of `affAdd p q` forces the distinct-`x` condition.  This is
the bridge from the phase's `ConstraintsHold.Soundness` hypothesis to the
`hDx` argument of `affAdd_sound`, so that parents can discharge it from the
constraints instead of assuming it. -/
theorem affAdd_dx (env : Environment Fp) (p q : Pt) (n : Nat)
    (h : ConstraintsHold.Soundness env ((affAdd p q).operations n)) :
    Expression.eval env q.1 - Expression.eval env p.1 ≠ 0 := by
  simp only [affAdd, nonzero, circuit_norm, pm] at h
  obtain ⟨r1, -, -, -⟩ := h
  exact nonzero_spec (inv := env.get n) r1

/-- The four rows of `affDouble p` at offset `n` give `2 • p`, with the output at
`n + 2`, `n + 3` when `p.x` is a wire. -/
theorem affDouble_sound (env : Environment Fp) (p : Pt) (n : Nat) (hdeg : deg p.1 = 1)
    (hA : NS (Expression.eval env p.1) (Expression.eval env p.2))
    (hy : 2 * Expression.eval env p.2 ≠ 0)
    (h : ConstraintsHold.Soundness env ((affDouble p).operations n)) :
    ∃ hR : NS (env.get (n + 2)) (env.get (n + 3)),
      Affine.Point.some (env.get (n + 2)) (env.get (n + 3)) hR
        = 2 • Affine.Point.some (Expression.eval env p.1) (Expression.eval env p.2) hA := by
  have hml : matLen (.mul p.1 p.1) = 1 := matLen_mul_of_deg_one hdeg hdeg
  simp only [affDouble, mm, circuit_norm, pm] at h
  obtain ⟨r1, r2, r3, r4⟩ := h
  have hlen : Operations.localLength (mat (.mul p.1 p.1) n).2 = matLen (.mul p.1 p.1) :=
    mat_localLength_eq _ n
  rw [hlen, hml] at r2 r3 r4
  have hxx : Expression.eval env ((mat (.mul p.1 p.1) n).1)
      = Expression.eval env p.1 * Expression.eval env p.1 := by
    rw [mat_output_eq]
    rw [mat_eval_gen (.mul p.1 p.1) n env
      { assert := fun e => Expression.eval env e = 0
        lookup := fun l => l.Soundness env
        interact := fun i => i.Guarantees env
        subcircuit := fun {m} s => s.Assumptions env → s.Spec env }
      (fun x hx => hx) r1]
    simp only [Expression.eval]
  have h2 : (2 * Expression.eval env p.2) * env.get (n + 1)
      = 3 * (Expression.eval env p.1 * Expression.eval env p.1) + pa := by
    have h2' : Expression.eval env (sc 2 p.2) * env.get (n + 1)
        - Expression.eval env (sc 3 (mat (.mul p.1 p.1) n).1)
        = Expression.eval env (cst pa) := sub_eq_zero.mp r2
    rw [eval_sc, eval_sc, eval_cst, hxx] at h2'
    rw [eq_add_of_sub_eq h2']
    exact add_comm _ _
  have h3 : env.get (n + 2) = env.get (n + 1) * env.get (n + 1)
      - 2 * Expression.eval env p.1 := by
    have h3' : env.get (n + 1) * env.get (n + 1) - Expression.eval env (sc 2 p.1)
        = env.get (n + 2) := sub_eq_zero.mp r3
    rw [eval_sc] at h3'
    exact h3'.symm
  have h4 : env.get (n + 3) = env.get (n + 1) * (Expression.eval env p.1 - env.get (n + 2))
      - Expression.eval env p.2 := by
    have h4' : env.get (n + 1) * (Expression.eval env p.1 - env.get (n + 2))
        - Expression.eval env p.2 = env.get (n + 3) := sub_eq_zero.mp r4
    exact h4'.symm
  exact affDoubleEqs_group #v[Expression.eval env p.1, Expression.eval env p.2]
    (env.get (n + 2), env.get (n + 3)) hA hy ⟨env.get (n + 1), h2, h3, h4⟩

/-! ## Composition of block soundness

The phases are `do`-blocks of gadget calls.  `soundness_bind` splits the
constraints of `c >>= f` into the constraints of `c` and those of the
continuation, so a phase can be peeled one gadget at a time without ever
unfolding a whole `do`-block at once. -/

theorem soundness_bind {α β : Type} (env : Environment Fp) (c : C α) (f : α → C β) (n : ℕ)
    (h : ConstraintsHold.Soundness env ((c >>= f).operations n)) :
    ConstraintsHold.Soundness env (c.operations n) ∧
      ConstraintsHold.Soundness env ((f (c.output n)).operations (n + c.localLength n)) := by
  simp only [ConstraintsHold.Soundness, Circuit.operations, Circuit.output, Circuit.localLength,
    bind_snd, Operations.forAllNoOffset_append] at h ⊢
  exact h

/-- Projection-level form of `affAdd_localLength`, matching the shape that
appears inside `do`-block offsets. -/
theorem affAdd_localLength' (p q : Pt) (n : ℕ) :
    Operations.localLength (affAdd p q n).2 = 4 := affAdd_localLength p q n

/-- Projection-level form of `affDouble_localLength`. -/
theorem affDouble_localLength' {p : Pt} (hx : deg p.1 = 1) (n : ℕ) :
    Operations.localLength (affDouble p n).2 = 4 := affDouble_localLength hx n

/-! ## Negation -/

/-- On P-256 (`a₁ = a₃ = 0`) the negated `y`-coordinate is `-y`. -/
theorem negY_eq_neg (x y : Fp) : Affine.negY Wp x y = -y := by
  dsimp [Affine.negY, Wp, StandardECDSA.Math.AffineBridge.W, CurveParameters.toMathlib]
  ring

/-- Nonsingularity is preserved by `y ↦ -y`. -/
theorem negPt_ns {x y : Fp} (h : NS x y) : NS x (-y) := by
  have h' : NS x (Affine.negY Wp x y) := (Affine.nonsingular_neg (W' := Wp) x y).mpr h
  rwa [negY_eq_neg] at h'

/-- `negPt` is group negation. -/
theorem negPt_group (x y : Fp) (h : NS x y) :
    Affine.Point.some x (-y) (negPt_ns h) = - Affine.Point.some x y h := by
  rw [Affine.Point.neg_some]
  simp only [Affine.Point.some.injEq]
  exact ⟨trivial, (negY_eq_neg x y).symm⟩

/-! ## Output coordinates of the affine gadgets -/

theorem affAdd_output (p q : Pt) (n : ℕ) :
    (affAdd p q n).1 = (var ⟨n + 2⟩, var ⟨n + 3⟩) := by
  simp only [affAdd, bind_fst, bind_snd, pure_fst, pure_snd, witnessField_fst,
    witnessField_snd, assertZero_snd, nonzero, localLength_witness,
    localLength_assert, Operations.append_localLength, Operations.localLength, Nat.add_zero,
    Nat.zero_add]

theorem affDouble_output (p : Pt) (n : ℕ) :
    (affDouble p n).1 = (var ⟨n + matLen (.mul p.1 p.1) + 1⟩,
      var ⟨n + matLen (.mul p.1 p.1) + 2⟩) := by
  simp only [affDouble, bind_fst, bind_snd, pure_fst, pure_snd, witnessField_fst,
    witnessField_snd, assertZero_snd, mm, mat_output_eq, mat_localLength_eq,
    localLength_witness, localLength_assert, Operations.append_localLength, Operations.localLength,
    Nat.add_zero, Nat.zero_add]

theorem affAdd_out_fst (p q : Pt) (env : Environment Fp) (n : ℕ) :
    Expression.eval env ((affAdd p q n).1.1) = env.get (n + 2) := by
  rw [affAdd_output]
  rfl

theorem affAdd_out_snd (p q : Pt) (env : Environment Fp) (n : ℕ) :
    Expression.eval env ((affAdd p q n).1.2) = env.get (n + 3) := by
  rw [affAdd_output]
  rfl

theorem affDouble_out_fst {p : Pt} (hx : deg p.1 = 1) (env : Environment Fp) (n : ℕ) :
    Expression.eval env ((affDouble p n).1.1) = env.get (n + 2) := by
  have hml : matLen (.mul p.1 p.1) = 1 := matLen_mul_of_deg_one hx hx
  rw [affDouble_output]
  simp only [hml, Expression.eval]

theorem affDouble_out_snd {p : Pt} (hx : deg p.1 = 1) (env : Environment Fp) (n : ℕ) :
    Expression.eval env ((affDouble p n).1.2) = env.get (n + 3) := by
  have hml : matLen (.mul p.1 p.1) = 1 := matLen_mul_of_deg_one hx hx
  rw [affDouble_output]
  simp only [hml, Expression.eval]

/-! ## Congruence helpers -/

theorem ns_congr {x x' y y' : Fp} (hx : x = x') (hy : y = y') (h : NS x' y') : NS x y := by
  rw [hx, hy]; exact h

theorem some_congr {x x' y y' : Fp} (hx : x = x') (hy : y = y') (h : NS x y) (h' : NS x' y') :
    Affine.Point.some x y h = Affine.Point.some x' y' h' := by
  cases hx; cases hy
  rfl

theorem nsmul_two_add (P : Affine.Point Wp) : 2 • P + P = 3 • P := by
  simp only [two_nsmul, three_nsmul]; abel

/-- `Expression.eval` distributes over negation (local copy of Clean's `eval_neg`). -/
theorem eval_neg' (env : Environment Fp) (a : E) :
    Expression.eval env (-a) = -Expression.eval env a := by
  simp only [circuit_norm]

/-- `negPt` congruence at the `Affine.Point.some` level. -/
theorem negPt_some_congr (env : Environment Fp) (p : Pt)
    {hL : NS (Expression.eval env (negPt p).1) (Expression.eval env (negPt p).2)}
    (h' : NS (Expression.eval env p.1) (-(Expression.eval env p.2))) :
    Affine.Point.some (Expression.eval env (negPt p).1) (Expression.eval env (negPt p).2) hL
      = Affine.Point.some (Expression.eval env p.1) (-(Expression.eval env p.2)) h' :=
  some_congr (hx := rfl) (hy := eval_neg' env p.2) (h := hL) (h' := h')

/-! ## Group semantics of the shifted-table phase -/

/-- **Shifted-table contract (plan §3A).**

Given `H`, `Q`, `R` on the curve, `2·H.y ≠ 0` and the five distinct-`x`
conditions the eight affine additions need, every satisfying assignment of
`shiftedTables h q r` at offset `n` makes the eight table entries equal
`±3H + b₀·Q + b₁·R` in the group, in table order `rBit + 2·tBit`.

The construction never asks for affine coordinates of the unshifted `Q + R`, so
it is available when `Q + R = O` or `Q = R`; those cases only make some of the
distinct-`x` conditions unsatisfiable, which is exactly what the global offset
theorem has to avoid. -/
theorem shiftedTables_spec (env : Environment Fp) (h q r : Pt) (n : ℕ) (hdeg : deg h.1 = 1)
    (hH : NS (Expression.eval env h.1) (Expression.eval env h.2))
    (hQ : NS (Expression.eval env q.1) (Expression.eval env q.2))
    (hR : NS (Expression.eval env r.1) (Expression.eval env r.2))
    (hy : 2 * Expression.eval env h.2 ≠ 0)
    (hdx1 : Expression.eval env h.1 - env.get (n + 2) ≠ 0)
    (hdx2 : Expression.eval env q.1 - env.get (n + 6) ≠ 0)
    (hdx3 : Expression.eval env r.1 - env.get (n + 6) ≠ 0)
    (hdx4 : Expression.eval env r.1 - env.get (n + 10) ≠ 0)
    (hdx5 : Expression.eval env r.1 - env.get (n + 22) ≠ 0)
    (hc : ConstraintsHold.Soundness env ((shiftedTables h q r).operations n)) :
    ∃ (h0 : NS (env.get (n + 6)) (env.get (n + 7)))
      (h1 : NS (env.get (n + 10)) (env.get (n + 11)))
      (h2 : NS (env.get (n + 14)) (env.get (n + 15)))
      (h3 : NS (env.get (n + 18)) (env.get (n + 19)))
      (h4 : NS (env.get (n + 6)) (-(env.get (n + 7))))
      (h5 : NS (env.get (n + 22)) (env.get (n + 23)))
      (h6 : NS (env.get (n + 26)) (env.get (n + 27)))
      (h7 : NS (env.get (n + 30)) (env.get (n + 31))),
      Affine.Point.some (env.get (n + 6)) (env.get (n + 7)) h0
          = 3 • Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH ∧
      Affine.Point.some (env.get (n + 10)) (env.get (n + 11)) h1
          = 3 • Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH
            + Affine.Point.some (Expression.eval env q.1) (Expression.eval env q.2) hQ ∧
      Affine.Point.some (env.get (n + 14)) (env.get (n + 15)) h2
          = 3 • Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH
            + Affine.Point.some (Expression.eval env r.1) (Expression.eval env r.2) hR ∧
      Affine.Point.some (env.get (n + 18)) (env.get (n + 19)) h3
          = 3 • Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH
            + Affine.Point.some (Expression.eval env q.1) (Expression.eval env q.2) hQ
            + Affine.Point.some (Expression.eval env r.1) (Expression.eval env r.2) hR ∧
      Affine.Point.some (env.get (n + 6)) (-(env.get (n + 7))) h4
          = -(3 • Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH) ∧
      Affine.Point.some (env.get (n + 22)) (env.get (n + 23)) h5
          = -(3 • Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH)
            + Affine.Point.some (Expression.eval env q.1) (Expression.eval env q.2) hQ ∧
      Affine.Point.some (env.get (n + 26)) (env.get (n + 27)) h6
          = -(3 • Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH)
            + Affine.Point.some (Expression.eval env r.1) (Expression.eval env r.2) hR ∧
      Affine.Point.some (env.get (n + 30)) (env.get (n + 31)) h7
          = -(3 • Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH)
            + Affine.Point.some (Expression.eval env q.1) (Expression.eval env q.2) hQ
            + Affine.Point.some (Expression.eval env r.1) (Expression.eval env r.2) hR := by
  simp only [shiftedTables, circuit_norm] at hc
  simp only [affAdd_localLength', affDouble_localLength' hdeg] at hc
  obtain ⟨a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6, c1, c2, c3⟩ := hc
  have h1 : ConstraintsHold.Soundness env ((affDouble h).operations n) := a1
  have h2 : ConstraintsHold.Soundness env ((affAdd (affDouble h n).1 h).operations (n + 4)) := a2
  have h3 : ConstraintsHold.Soundness env
      ((affAdd (affAdd (affDouble h n).1 h (n + 4)).1 q).operations (n + 8)) := a3
  have h4 : ConstraintsHold.Soundness env
      ((affAdd (affAdd (affDouble h n).1 h (n + 4)).1 r).operations (n + 12)) := a4
  have h5 : ConstraintsHold.Soundness env
      ((affAdd (affAdd (affAdd (affDouble h n).1 h (n + 4)).1 q (n + 8)).1 r).operations
        (n + 16)) := a5
  have h6 : ConstraintsHold.Soundness env
      ((affAdd (negPt (affAdd (affDouble h n).1 h (n + 4)).1) q).operations (n + 20)) := a6
  have h7 : ConstraintsHold.Soundness env
      ((affAdd (negPt (affAdd (affDouble h n).1 h (n + 4)).1) r).operations (n + 24)) := b1
  have h8 : ConstraintsHold.Soundness env
      ((affAdd (affAdd (negPt (affAdd (affDouble h n).1 h (n + 4)).1) q (n + 20)).1 r).operations
        (n + 28)) := ⟨b2, b3, b4, b5, b6, c1, c2, c3⟩
  -- `2H`
  obtain ⟨hP0, e0⟩ := affDouble_sound env h n hdeg hH hy h1
  -- `3H = 2H + H`
  obtain ⟨hP1, e1⟩ := affAdd_sound env (affDouble h n).1 h (n + 4)
    (ns_congr (affDouble_out_fst hdeg env n) (affDouble_out_snd hdeg env n) hP0) hH
    (by rw [affDouble_out_fst hdeg env n]; exact hdx1) h2
  have e1' : Affine.Point.some (env.get (n + 6)) (env.get (n + 7)) hP1
      = 3 • Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH := by
    rw [e1]
    rw [some_congr (hx := affDouble_out_fst hdeg env n)
      (hy := affDouble_out_snd hdeg env n) (h' := hP0)]
    rw [e0]
    exact nsmul_two_add _
  -- `3H + Q`
  obtain ⟨hP2, e2⟩ := affAdd_sound env (affAdd (affDouble h n).1 h (n + 4)).1 q (n + 8)
    (ns_congr (affAdd_out_fst _ _ env (n + 4)) (affAdd_out_snd _ _ env (n + 4)) hP1) hQ hdx2 h3
  have e2' : Affine.Point.some (env.get (n + 10)) (env.get (n + 11)) hP2
      = 3 • Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH
        + Affine.Point.some (Expression.eval env q.1) (Expression.eval env q.2) hQ := by
    rw [e2]
    rw [some_congr (hx := affAdd_out_fst _ _ env (n + 4))
      (hy := affAdd_out_snd _ _ env (n + 4)) (h' := hP1)]
    rw [e1']
  -- `3H + R`
  obtain ⟨hP3, e3⟩ := affAdd_sound env (affAdd (affDouble h n).1 h (n + 4)).1 r (n + 12)
    (ns_congr (affAdd_out_fst _ _ env (n + 4)) (affAdd_out_snd _ _ env (n + 4)) hP1) hR hdx3 h4
  have e3' : Affine.Point.some (env.get (n + 14)) (env.get (n + 15)) hP3
      = 3 • Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH
        + Affine.Point.some (Expression.eval env r.1) (Expression.eval env r.2) hR := by
    rw [e3]
    rw [some_congr (hx := affAdd_out_fst _ _ env (n + 4))
      (hy := affAdd_out_snd _ _ env (n + 4)) (h' := hP1)]
    rw [e1']
  -- `3H + Q + R`
  obtain ⟨hP4, e4⟩ := affAdd_sound env
    (affAdd (affAdd (affDouble h n).1 h (n + 4)).1 q (n + 8)).1 r (n + 16)
    (ns_congr (affAdd_out_fst _ _ env (n + 8)) (affAdd_out_snd _ _ env (n + 8)) hP2) hR hdx4 h5
  have e4' : Affine.Point.some (env.get (n + 18)) (env.get (n + 19)) hP4
      = 3 • Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH
        + Affine.Point.some (Expression.eval env q.1) (Expression.eval env q.2) hQ
        + Affine.Point.some (Expression.eval env r.1) (Expression.eval env r.2) hR := by
    rw [e4]
    rw [some_congr (hx := affAdd_out_fst _ _ env (n + 8))
      (hy := affAdd_out_snd _ _ env (n + 8)) (h' := hP2)]
    rw [e2']
  -- `-3H`
  have e5' : Affine.Point.some (env.get (n + 6)) (-(env.get (n + 7))) (negPt_ns hP1)
      = -(3 • Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH) := by
    rw [negPt_group (env.get (n + 6)) (env.get (n + 7)) hP1, e1']
  -- `-3H + Q`
  obtain ⟨hP5, e5⟩ := affAdd_sound env (negPt (affAdd (affDouble h n).1 h (n + 4)).1) q (n + 20)
    (ns_congr (rfl : Expression.eval env (negPt (affAdd (affDouble h n).1 h (n + 4)).1).1
        = Expression.eval env (affAdd (affDouble h n).1 h (n + 4)).1.1)
      (eval_neg' env _) (negPt_ns (ns_congr (affAdd_out_fst _ _ env (n + 4))
        (affAdd_out_snd _ _ env (n + 4)) hP1))) hQ hdx2 h6
  have e6' : Affine.Point.some (env.get (n + 22)) (env.get (n + 23)) hP5
      = -(3 • Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH)
        + Affine.Point.some (Expression.eval env q.1) (Expression.eval env q.2) hQ := by
    rw [e5]
    rw [negPt_some_congr env (affAdd (affDouble h n).1 h (n + 4)).1
      (h' := negPt_ns (ns_congr (affAdd_out_fst _ _ env (n + 4))
        (affAdd_out_snd _ _ env (n + 4)) hP1))]
    rw [some_congr (hx := affAdd_out_fst _ _ env (n + 4))
      (hy := congrArg (fun z : Fp => -z) (affAdd_out_snd _ _ env (n + 4)))
      (h' := negPt_ns hP1)]
    rw [e5']
  -- `-3H + R`
  obtain ⟨hP6, e6⟩ := affAdd_sound env (negPt (affAdd (affDouble h n).1 h (n + 4)).1) r (n + 24)
    (ns_congr (rfl : Expression.eval env (negPt (affAdd (affDouble h n).1 h (n + 4)).1).1
        = Expression.eval env (affAdd (affDouble h n).1 h (n + 4)).1.1)
      (eval_neg' env _) (negPt_ns (ns_congr (affAdd_out_fst _ _ env (n + 4))
        (affAdd_out_snd _ _ env (n + 4)) hP1))) hR hdx3 h7
  have e7' : Affine.Point.some (env.get (n + 26)) (env.get (n + 27)) hP6
      = -(3 • Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH)
        + Affine.Point.some (Expression.eval env r.1) (Expression.eval env r.2) hR := by
    rw [e6]
    rw [negPt_some_congr env (affAdd (affDouble h n).1 h (n + 4)).1
      (h' := negPt_ns (ns_congr (affAdd_out_fst _ _ env (n + 4))
        (affAdd_out_snd _ _ env (n + 4)) hP1))]
    rw [some_congr (hx := affAdd_out_fst _ _ env (n + 4))
      (hy := congrArg (fun z : Fp => -z) (affAdd_out_snd _ _ env (n + 4)))
      (h' := negPt_ns hP1)]
    rw [e5']
  -- `-3H + Q + R`
  obtain ⟨hP7, e7⟩ := affAdd_sound env
    (affAdd (negPt (affAdd (affDouble h n).1 h (n + 4)).1) q (n + 20)).1 r (n + 28)
    (ns_congr (affAdd_out_fst _ _ env (n + 20)) (affAdd_out_snd _ _ env (n + 20)) hP5) hR hdx5 h8
  have e8' : Affine.Point.some (env.get (n + 30)) (env.get (n + 31)) hP7
      = -(3 • Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH)
        + Affine.Point.some (Expression.eval env q.1) (Expression.eval env q.2) hQ
        + Affine.Point.some (Expression.eval env r.1) (Expression.eval env r.2) hR := by
    rw [e7]
    rw [some_congr (hx := affAdd_out_fst _ _ env (n + 20))
      (hy := affAdd_out_snd _ _ env (n + 20)) (h' := hP5)]
    rw [e6']
  exact ⟨hP1, hP2, hP3, hP4, negPt_ns hP1, hP5, hP6, hP7,
    e1', e2', e3', e4', e5', e6', e7', e8'⟩

/-- **The shifted-table phase's distinct-`x` conditions follow from its rows.**

The eight affine additions each carry an inverse row, so the five distinct-`x`
conditions of `shiftedTables_spec` are consequences of the phase's constraints.
The two `-3H` additions reuse `hdx2`/`hdx3` because `negPt` only negates the
`y`-coordinate. -/
theorem shiftedTables_dx (env : Environment Fp) (h q r : Pt) (n : ℕ) (hdeg : deg h.1 = 1)
    (hc : ConstraintsHold.Soundness env ((shiftedTables h q r).operations n)) :
    (Expression.eval env h.1 - env.get (n + 2) ≠ 0) ∧
    (Expression.eval env q.1 - env.get (n + 6) ≠ 0) ∧
    (Expression.eval env r.1 - env.get (n + 6) ≠ 0) ∧
    (Expression.eval env r.1 - env.get (n + 10) ≠ 0) ∧
    (Expression.eval env r.1 - env.get (n + 22) ≠ 0) := by
  simp only [shiftedTables, circuit_norm] at hc
  simp only [affAdd_localLength', affDouble_localLength' hdeg] at hc
  obtain ⟨a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6, c1, c2, c3⟩ := hc
  have h2 : ConstraintsHold.Soundness env ((affAdd (affDouble h n).1 h).operations (n + 4)) := a2
  have h3 : ConstraintsHold.Soundness env
      ((affAdd (affAdd (affDouble h n).1 h (n + 4)).1 q).operations (n + 8)) := a3
  have h4 : ConstraintsHold.Soundness env
      ((affAdd (affAdd (affDouble h n).1 h (n + 4)).1 r).operations (n + 12)) := a4
  have h5 : ConstraintsHold.Soundness env
      ((affAdd (affAdd (affAdd (affDouble h n).1 h (n + 4)).1 q (n + 8)).1 r).operations
        (n + 16)) := a5
  have h8 : ConstraintsHold.Soundness env
      ((affAdd (affAdd (negPt (affAdd (affDouble h n).1 h (n + 4)).1) q (n + 20)).1 r).operations
        (n + 28)) := ⟨b2, b3, b4, b5, b6, c1, c2, c3⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← affDouble_out_fst hdeg env n]
    exact affAdd_dx env (affDouble h n).1 h (n + 4) h2
  · rw [← affAdd_out_fst (affDouble h n).1 h env (n + 4)]
    exact affAdd_dx env (affAdd (affDouble h n).1 h (n + 4)).1 q (n + 8) h3
  · rw [← affAdd_out_fst (affDouble h n).1 h env (n + 4)]
    exact affAdd_dx env (affAdd (affDouble h n).1 h (n + 4)).1 r (n + 12) h4
  · rw [← affAdd_out_fst (affAdd (affDouble h n).1 h (n + 4)).1 q env (n + 8)]
    exact affAdd_dx env (affAdd (affAdd (affDouble h n).1 h (n + 4)).1 q (n + 8)).1 r (n + 16) h5
  · rw [← affAdd_out_fst (negPt (affAdd (affDouble h n).1 h (n + 4)).1) q env (n + 20)]
    exact affAdd_dx env (affAdd (negPt (affAdd (affDouble h n).1 h (n + 4)).1) q (n + 20)).1 r
      (n + 28) h8

end StandardECDSA.Phases
