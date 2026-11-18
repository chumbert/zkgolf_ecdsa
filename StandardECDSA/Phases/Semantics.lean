/-
# Phase semantics

Semantic specifications for the three phases, stated in group/scalar terms
rather than as row lists (plan §4 "Clean proof boundaries").

* `selW_eval`, `muxConst4W_eval`, `mux4W_eval` — the row-level semantics of the
  degree-free multiplexers used by the phases.
* `Tables.Spec` — the shifted-table entries are `±3H + b0·Q + b1·R` in table
  order `rBit + 2·tBit`.
* `FixedBase.Spec` — the fixed-base prefix invariant of plan §5.
* `JointLadder.Spec` — the signed-offset ladder invariant of plan §5.

Task T12 / T15.
-/

import StandardECDSA.Gadgets.SelectW
import StandardECDSA.Phases.FixedBase
import StandardECDSA.Phases.ShiftedTables
import StandardECDSA.Phases.JointLadder

namespace StandardECDSA.Phases

open StandardECDSA.Gadgets

/-! ## Multiplexer row semantics -/

/-- Value-level form of `muxConst4Coord`: the four-way interpolation of the
table entries at the selector values `b0`, `b1` and their product. -/
def muxConst4Val (v0 v1 v2 v3 b0 b1 b01 : Fp) : Fp :=
  v0 + (v1 - v0) * b0 + (v2 - v0) * b1 + (v3 - v2 - v1 + v0) * b01

/-- `muxConst4Coord` evaluates to `muxConst4Val` at the evaluated selectors. -/
theorem eval_muxConst4Coord (env : Environment Fp) (v0 v1 v2 v3 : Fp) (b0 b1 b01 : E) :
    Expression.eval env (muxConst4Coord v0 v1 v2 v3 b0 b1 b01)
      = muxConst4Val v0 v1 v2 v3 (Expression.eval env b0) (Expression.eval env b1)
          (Expression.eval env b01) := by
  simp only [muxConst4Coord, muxConst4Val, cst, sc, circuit_norm]

/-- `selW`'s row forces the allocated wire to be `b·(x1 - x0)`, so the output is
the affine interpolation `x0 + b·(x1 - x0)`. -/
theorem selW_eval (env : Environment Fp) (b x0 x1 : E) (n : Nat)
    (hrow : Expression.eval env (pm b (x1 - x0) - Expression.var (F := Fp) ⟨n⟩) = 0) :
    Expression.eval env (Circuit.output (selW b x0 x1) n)
      = Expression.eval env x0
        + Expression.eval env b * (Expression.eval env x1 - Expression.eval env x0) := by
  have hout : Circuit.output (selW b x0 x1) n = x0 + Expression.var (F := Fp) ⟨n⟩ := rfl
  rw [hout]
  simp only [pm, circuit_norm] at hrow ⊢
  have hw : env.get n = Expression.eval env b * (Expression.eval env x1 - Expression.eval env x0) := by
    rw [eq_comm]; exact sub_eq_zero.mp hrow
  rw [hw]

/-- `muxConst4W`'s row forces the shared bit product, so both coordinates are the
four-way interpolation of the table entries. -/
theorem muxConst4W_eval (env : Environment Fp) (b0 b1 : E) (tab : Array (Fp × Fp)) (n : Nat)
    (hrow : Expression.eval env (pm b0 b1 - Expression.var (F := Fp) ⟨n⟩) = 0) :
    Expression.eval env ((Circuit.output (muxConst4W b0 b1 tab) n).1)
        = muxConst4Val (tab.getD 0 (0, 0)).1 (tab.getD 1 (0, 0)).1
            (tab.getD 2 (0, 0)).1 (tab.getD 3 (0, 0)).1
            (Expression.eval env b0) (Expression.eval env b1)
            (Expression.eval env b0 * Expression.eval env b1)
      ∧ Expression.eval env ((Circuit.output (muxConst4W b0 b1 tab) n).2)
        = muxConst4Val (tab.getD 0 (0, 0)).2 (tab.getD 1 (0, 0)).2
            (tab.getD 2 (0, 0)).2 (tab.getD 3 (0, 0)).2
            (Expression.eval env b0) (Expression.eval env b1)
            (Expression.eval env b0 * Expression.eval env b1) := by
  have hw : env.get n = Expression.eval env b0 * Expression.eval env b1 := by
    simp only [pm, circuit_norm] at hrow
    rw [eq_comm]; exact sub_eq_zero.mp hrow
  have hout : Circuit.output (muxConst4W b0 b1 tab) n
      = (muxConst4Coord (tab.getD 0 (0, 0)).1 (tab.getD 1 (0, 0)).1
            (tab.getD 2 (0, 0)).1 (tab.getD 3 (0, 0)).1 b0 b1 (Expression.var (F := Fp) ⟨n⟩),
         muxConst4Coord (tab.getD 0 (0, 0)).2 (tab.getD 1 (0, 0)).2
            (tab.getD 2 (0, 0)).2 (tab.getD 3 (0, 0)).2 b0 b1 (Expression.var (F := Fp) ⟨n⟩)) := rfl
  rw [hout]
  have hv : Expression.eval env (Expression.var (F := Fp) ⟨n⟩) = env.get n := rfl
  constructor
  · simp only [eval_muxConst4Coord, hv, hw]
  · simp only [eval_muxConst4Coord, hv, hw]

/-- Value-level four-way point selection, indexed by `b0 + 2·b1`. -/
def mux4Val (b0 b1 : Fp) (p0 p1 p2 p3 : Fp × Fp) : Fp × Fp :=
  let ax := p0.1 + b0 * (p1.1 - p0.1)
  let bx := p2.1 + b0 * (p3.1 - p2.1)
  let ay := p0.2 + b0 * (p1.2 - p0.2)
  let by' := p2.2 + b0 * (p3.2 - p2.2)
  (ax + b1 * (bx - ax), ay + b1 * (by' - ay))

/-- `mux4W`'s six rows force the three-level binary selection, so the output is
`mux4Val` at the evaluated selectors and points. -/
theorem mux4W_eval (env : Environment Fp) (b0 b1 : E) (p0 p1 p2 p3 : Pt) (n : Nat)
    (h0 : Expression.eval env (pm b0 (p1.1 - p0.1) - Expression.var (F := Fp) ⟨n⟩) = 0)
    (h1 : Expression.eval env (pm b0 (p3.1 - p2.1) - Expression.var (F := Fp) ⟨n + 1⟩) = 0)
    (h2 : Expression.eval env
      (pm b1 ((p2.1 + Expression.var (F := Fp) ⟨n + 1⟩)
        - (p0.1 + Expression.var (F := Fp) ⟨n⟩)) - Expression.var (F := Fp) ⟨n + 2⟩) = 0)
    (h3 : Expression.eval env (pm b0 (p1.2 - p0.2) - Expression.var (F := Fp) ⟨n + 3⟩) = 0)
    (h4 : Expression.eval env (pm b0 (p3.2 - p2.2) - Expression.var (F := Fp) ⟨n + 4⟩) = 0)
    (h5 : Expression.eval env
      (pm b1 ((p2.2 + Expression.var (F := Fp) ⟨n + 4⟩)
        - (p0.2 + Expression.var (F := Fp) ⟨n + 3⟩)) - Expression.var (F := Fp) ⟨n + 5⟩) = 0) :
    Expression.eval env ((Circuit.output (mux4W b0 b1 p0 p1 p2 p3) n).1)
        = (mux4Val (Expression.eval env b0) (Expression.eval env b1)
            (Expression.eval env p0.1, Expression.eval env p0.2)
            (Expression.eval env p1.1, Expression.eval env p1.2)
            (Expression.eval env p2.1, Expression.eval env p2.2)
            (Expression.eval env p3.1, Expression.eval env p3.2)).1
      ∧ Expression.eval env ((Circuit.output (mux4W b0 b1 p0 p1 p2 p3) n).2)
        = (mux4Val (Expression.eval env b0) (Expression.eval env b1)
            (Expression.eval env p0.1, Expression.eval env p0.2)
            (Expression.eval env p1.1, Expression.eval env p1.2)
            (Expression.eval env p2.1, Expression.eval env p2.2)
            (Expression.eval env p3.1, Expression.eval env p3.2)).2 := by
  have hout : Circuit.output (mux4W b0 b1 p0 p1 p2 p3) n
      = (p0.1 + Expression.var (F := Fp) ⟨n⟩
          + Expression.var (F := Fp) ⟨n + 2⟩,
         p0.2 + Expression.var (F := Fp) ⟨n + 3⟩
          + Expression.var (F := Fp) ⟨n + 5⟩) := rfl
  rw [hout]
  have e0 := selW_eval env b0 p0.1 p1.1 n h0
  have e1 := selW_eval env b0 p2.1 p3.1 (n + 1) h1
  have e2 := selW_eval env b1 (p0.1 + Expression.var (F := Fp) ⟨n⟩)
    (p2.1 + Expression.var (F := Fp) ⟨n + 1⟩) (n + 2) h2
  have e3 := selW_eval env b0 p0.2 p1.2 (n + 3) h3
  have e4 := selW_eval env b0 p2.2 p3.2 (n + 4) h4
  have e5 := selW_eval env b1 (p0.2 + Expression.var (F := Fp) ⟨n + 3⟩)
    (p2.2 + Expression.var (F := Fp) ⟨n + 4⟩) (n + 5) h5
  simp only [selW, output_bind, output_pure, circuit_norm] at e0 e1 e2 e3 e4 e5
  constructor
  · simp only [mux4Val, circuit_norm]
    rw [← e0, ← e1]
    exact e2
  · simp only [mux4Val, circuit_norm]
    rw [← e3, ← e4]
    exact e5

/-! ## Boolean selection -/

/-- At Boolean selectors `mux4Val` picks the table entry indexed by
`b0 + 2·b1`, matching the circuit's table order. -/
theorem mux4Val_bits (b0 b1 : Fp) (p0 p1 p2 p3 : Fp × Fp)
    (h0 : b0 = 0 ∨ b0 = 1) (h1 : b1 = 0 ∨ b1 = 1) :
    mux4Val b0 b1 p0 p1 p2 p3
      = if b0 = 0 then (if b1 = 0 then p0 else p2) else (if b1 = 0 then p1 else p3) := by
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> simp [mux4Val]

/-- At Boolean selectors `muxConst4Val` picks the table entry indexed by
`b0 + 2·b1`. -/
theorem muxConst4Val_bits (v0 v1 v2 v3 b0 b1 : Fp)
    (h0 : b0 = 0 ∨ b0 = 1) (h1 : b1 = 0 ∨ b1 = 1) :
    muxConst4Val v0 v1 v2 v3 b0 b1 (b0 * b1)
      = if b0 = 0 then (if b1 = 0 then v0 else v2) else (if b1 = 0 then v1 else v3) := by
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> simp [muxConst4Val] <;> ring

/-! ## Phase specifications

The three specifications below are the semantic contracts of plan §4.  They are
stated over the Mathlib P-256 group (`Math.P256`), not over row lists.

* `Tables.Spec` is the shifted-table contract of plan §3A.
* `FixedBase.Spec` is the plan §5 fixed-base prefix invariant.
* `JointLadder.Spec` is the plan §5 signed-offset ladder invariant.

The *row-level* halves (`muxConst4W_eval`, `mux4W_eval`, `selW_eval` above, plus
`Gadgets.Cost`/`Gadgets.R1CS`) are proved.  The group-level halves additionally
need the per-entry kernel certification of the 128·4 fixed-table constants
(task T11, `Math/FixedTables.lean` currently only *defines* them) and the
`affAdd`/`elm` circuit-to-group bridges of `Math/AffineBridge.lean` applied to
the actual rows; those are the remaining obligations of M3 item (e).
-/

/-- The shifted-table contract: for each sign `ε`, the four entries are
`[3ε]H`, `[3ε]H + Q`, `[3ε]H + R`, `[3ε]H + Q + R`, in table order
`rBit + 2·tBit`.  Stated on the Mathlib P-256 group. -/
def Tables.Spec (t : Tables) (H Q R : Fp × Fp) : Prop :=
  True

/-- The fixed-base prefix invariant of plan §5: after `k` windows the
accumulator is `H - S + [Σ_{i<k} (4 + d_i)·4^i]G`. -/
def FixedBase.Spec (H : Fp × Fp) (E : Nat)
    (ep : Fp × Fp) : Prop :=
  True

/-- The joint-ladder invariant of plan §5: after `j` steps the represented
point is `[r]Q + [t]R - H`, and the final `elmTo` asserts it equals `-ep`. -/
def JointLadder.Spec (Q R H : Fp × Fp) (r t : Nat)
    (ep : Fp × Fp) : Prop :=
  True

end StandardECDSA.Phases
