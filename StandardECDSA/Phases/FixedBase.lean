/-
# Fixed-base phase: `ep = H + [E]G`

Ported from the pinned `circuit_baseline` revision
(`3a1bd20749ae0b6400a158651dba64a2c5fc58ff`), `Baseline/Projected/Offset.lean`.

The phase starts from `H - S` with `S = [4·(4^128 - 1)/3]G` and adds, for each of
the 128 windows, the constant point `[(4 + d_i)·4^i]G` where
`d_i = eBit[2i] + 2·eBit[2i+1]`.  The prefix invariant (plan §5) is

```text
ep_k = H - S + Σ_{i<k} [(4 + d_i)·4^i]G,      ep_128 = H + [E]G
```

Cost: 1 initial `affAdd` plus 128 × (`muxConst4` + `affAdd`) = 644 allocations
and 644 rows.

Task T12 (fixed-base half).
-/

import StandardECDSA.Gadgets.Select
import StandardECDSA.Gadgets.Affine
import StandardECDSA.Math.FixedTables
import StandardECDSA.Gadgets.LocalLength
import StandardECDSA.Gadgets.SelectW

namespace StandardECDSA.Phases

open StandardECDSA.Gadgets

/-- One window of the fixed-base phase: add `[(4 + d_i)·4^i]G` to `ep`. -/
def fixedBaseBody (eb : Vector E 256) (tables : Array (Array (Fp × Fp))) (ep : Pt)
    (i : Fin 128) : C Pt := do
  let t ← muxConst4W (eb.get ⟨2 * i.val, by omega⟩) (eb.get ⟨2 * i.val + 1, by omega⟩)
    (tables.getD i.val #[])
  affAdd ep t

/-- Every window of the fixed-base phase allocates exactly five wires. -/
def fixedBaseBody_constantLength (eb : Vector E 256) (tables : Array (Array (Fp × Fp))) :
    Circuit.ConstantLength (fun (t : Pt × Fin 128) => fixedBaseBody eb tables t.1 t.2) where
  localLength := 5
  localLength_eq := by
    intro t n
    obtain ⟨ep, j⟩ := t
    simp only [fixedBaseBody, bind_snd, pure_snd,
      muxConst4W_localLength, affAdd_localLength,
      Circuit.localLength, Operations.append_localLength, Operations.localLength]

/-- The `x`-coordinate of the fixed-base shift `S = [4·(4^128-1)/3]G`.

Marked `irreducible` so that `whnf` never unfolds the 256-bit scalar
multiplication `mulG` hidden behind it.  Without this, every defeq check that
mentions the shift coordinates reduces `mulG` and blows the heartbeat budget. -/
@[irreducible] def shiftX : Fp := StandardECDSA.Math.FixedTables.fixedShift.1

/-- The `y`-coordinate of the fixed-base shift `S`.  See `shiftX`. -/
@[irreducible] def shiftY : Fp := StandardECDSA.Math.FixedTables.fixedShift.2

theorem shiftX_eq : shiftX = StandardECDSA.Math.FixedTables.fixedShift.1 := by
  with_unfolding_all rfl

theorem shiftY_eq : shiftY = StandardECDSA.Math.FixedTables.fixedShift.2 := by
  with_unfolding_all rfl

/-- The output of the 128-window fixed-base fold, sealed behind an
`@[irreducible]` definition.

`Expression.eval` is a pattern-matching `def`, so any definitional-unfolding
check that mentions `Expression.eval env ((fixedBase h eb n).1.1)` would `whnf`
the whole 128-step `foldlRange` and exceed the recursion/heartbeat budget.  By
returning `fixedBaseOut h eb n` from `fixedBase`, `(fixedBase h eb n).1` reduces
to the *stuck* term `fixedBaseOut h eb n` in one step, so such checks are cheap.
The fold is only unfolded where it is actually analysed, via
`fixedBaseOut_eq`. -/
@[irreducible] def fixedBaseOut (h : Pt) (eb : Vector E 256) (n : Nat) : Pt :=
  (Circuit.foldlRange 128 ((affAdd h (cst shiftX, cst (-shiftY))).output n)
    (fixedBaseBody eb StandardECDSA.Math.FixedTables.fixedTables)
    (fixedBaseBody_constantLength eb StandardECDSA.Math.FixedTables.fixedTables)).output (n + 4)

/-- Defining equation of `fixedBaseOut`. -/
theorem fixedBaseOut_eq (h : Pt) (eb : Vector E 256) (n : Nat) :
    fixedBaseOut h eb n
      = (Circuit.foldlRange 128 ((affAdd h (cst shiftX, cst (-shiftY))).output n)
          (fixedBaseBody eb StandardECDSA.Math.FixedTables.fixedTables)
          (fixedBaseBody_constantLength eb StandardECDSA.Math.FixedTables.fixedTables)).output (n + 4) := by
  unfold fixedBaseOut
  rfl

/-- The fixed-base phase.  `eb` holds the 256 digest bits, least significant
first.  Returns `ep = H + [E]G` in affine coordinates.

Written as an explicit lambda rather than a `do` block: with the `do` form,
`(fixedBase h eb).operations n` only reduces after destructuring the result of
the 128-window fold, so every defeq check that mentions the phase's operations
has to `whnf` the whole fold and blows the heartbeat budget.  The explicit form
reduces to a `++` in one step. -/
def fixedBase (h : Pt) (eb : Vector E 256) : C Pt := fun n =>
  let ops0 := (affAdd h (cst shiftX, cst (-shiftY)) n).2
  let r := Circuit.foldlRange 128 (affAdd h (cst shiftX, cst (-shiftY)) n).1
    (fixedBaseBody eb StandardECDSA.Math.FixedTables.fixedTables)
    (fixedBaseBody_constantLength eb StandardECDSA.Math.FixedTables.fixedTables)
    (n + Operations.localLength ops0)
  (fixedBaseOut h eb n, ops0 ++ r.2)

end StandardECDSA.Phases
