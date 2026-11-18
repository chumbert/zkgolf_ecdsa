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

namespace StandardECDSA.Phases

open StandardECDSA.Gadgets

/-- The fixed-base phase.  `eb` holds the 256 digest bits, least significant
first.  Returns `ep = H + [E]G` in affine coordinates. -/
def fixedBase (h : Pt) (eb : Array E) : C Pt := do
  let shift := StandardECDSA.Math.FixedTables.fixedShift
  let tables := StandardECDSA.Math.FixedTables.fixedTables
  let mut ep ← affAdd h (cst shift.1, cst (-shift.2))
  for i in [0:128] do
    let t ← muxConst4 (eb.getD (2 * i) (cst 0)) (eb.getD (2 * i + 1) (cst 0))
      (tables.getD i #[])
    ep ← affAdd ep t
  return ep

end StandardECDSA.Phases
