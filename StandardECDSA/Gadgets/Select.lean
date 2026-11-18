/-
# Multiplexer gadgets for the standard P-256 ECDSA circuit

Ported from the pinned `circuit_baseline` revision
(`3a1bd20749ae0b6400a158651dba64a2c5fc58ff`), `Baseline/Optimized.lean` and
`Baseline/Projected/Offset.lean`.

* `bitOf` extracts a Boolean bit of a witness value (1 allocation, 0 rows);
* `assertBool` constrains an expression to be Boolean (0 allocations, 1 row);
* `sel` is a two-way select (1 allocation, 1 row, free when the difference is
  constant);
* `mux8` is the three-level binary tree over eight entries used by the
  original-table lowering (kept for reference; the standard circuit does not
  use it);
* `muxConst4` selects among four *constant* points using one shared bit product
  for both coordinates (1 allocation, 1 row);
* `mux4` selects among four *variable* points with three two-way selects per
  coordinate (6 allocations, 6 rows).

Task T10.
-/

import StandardECDSA.Gadgets.Field

namespace StandardECDSA.Gadgets

/-- The `j`-th bit of the witness value `x`, as a fresh Boolean wire.
The Boolean constraint is *not* imposed here; callers use `assertBool`. -/
def bitOf (x : E) (j : Nat) : C E :=
  Circuit.witnessField (.ite (.bit (.expr x) j) (.const 1) (.const 0))

/-- `b` is Boolean: `b² = b`.  One R1CS row, no allocation. -/
def assertBool (b : E) : C Unit := Circuit.assertZero (.mul b b - b)

/-- `x0` if `b = 0`, `x1` if `b = 1`; free when `x1 - x0` is constant. -/
def sel (b x0 x1 : E) : C E := mat (x0 + .mul b (x1 - x0))

/-- Three-level binary tree over eight entries, indexed by `b0 + 2*b1 + 4*b2`. -/
def mux8 (b0 b1 b2 : E) (v : List E) : C E := do
  let g := fun i => v.getD i (cst 0)
  let l0 ← sel b0 (g 0) (g 1)
  let l1 ← sel b0 (g 2) (g 3)
  let l2 ← sel b0 (g 4) (g 5)
  let l3 ← sel b0 (g 6) (g 7)
  let m0 ← sel b1 l0 l1
  let m1 ← sel b1 l2 l3
  sel b2 m0 m1

/-- Constant four-way point mux; one shared bit product for both coordinates.
The table is a fixed-size `Array` of four entries, so no unchecked default
participates in semantic correctness. -/
def muxConst4 (b0 b1 : E) (tab : Array (Fp × Fp)) : C Pt := do
  let b01 ← mm b0 b1
  let coord (get : Fp × Fp → Fp) : E :=
    let v0 := get (tab.getD 0 (0, 0))
    let v1 := get (tab.getD 1 (0, 0))
    let v2 := get (tab.getD 2 (0, 0))
    let v3 := get (tab.getD 3 (0, 0))
    cst v0 + sc (v1 - v0) b0 + sc (v2 - v0) b1 + sc (v3 - v2 - v1 + v0) b01
  pure (coord Prod.fst, coord Prod.snd)

/-- Four-way variable point mux, indexed by `b0 + 2*b1`. -/
def mux4 (b0 b1 : E) (p0 p1 p2 p3 : Pt) : C Pt := do
  let coord (get : Pt → E) : C E := do
    let a ← sel b0 (get p0) (get p1)
    let b ← sel b0 (get p2) (get p3)
    sel b1 a b
  return (← coord Prod.fst, ← coord Prod.snd)

end StandardECDSA.Gadgets
