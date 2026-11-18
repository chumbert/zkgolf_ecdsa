/-
# Shifted-table phase: `±3H` plus `Q` and `R`

Ported from the pinned `circuit_baseline` revision
(`3a1bd20749ae0b6400a158651dba64a2c5fc58ff`), `Baseline/Projected/Offset.lean`,
with the plan §3A modification: the *original* Longfellow table (which needed
affine coordinates of the unshifted `Q + R`) is deleted, and only the two
shifted tables are built.

For each sign `ε ∈ {+1, -1}`:

```text
P0 = [3ε]H
P1 = P0 + Q
P2 = P0 + R
P3 = P1 + R
table_ε = [P0, P1, P2, P3]
```

This uses six ordinary affine additions and never asks for affine coordinates
of unshifted `Q + R`, so it works when `Q + R = O` or `Q = R`, provided the
chosen offset avoids the actual addition denominators.  Table order matches
`rBit + 2·tBit`.

Cost: `affDouble` (4/4) + `affAdd` (4/4) for `2H` and `3H`, plus six `affAdd`
(24/24) = 32 allocations and 32 rows.

Task T12 (table half).
-/

import StandardECDSA.Gadgets.Affine

namespace StandardECDSA.Phases

open StandardECDSA.Gadgets

/-- The two shifted tables, indexed by `rBit + 2·tBit`. -/
structure Tables where
  /-- `[3H, 3H+Q, 3H+R, 3H+Q+R]` -/
  plus : Array Pt
  /-- `[-3H, -3H+Q, -3H+R, -3H+Q+R]` -/
  minus : Array Pt

/-- Build both shifted tables from `H`, `Q` and `R`. -/
def shiftedTables (h q r : Pt) : C Tables := do
  let hh ← affDouble h
  let hhh ← affAdd hh h
  let nhhh := negPt hhh
  let p1 ← affAdd hhh q
  let p2 ← affAdd hhh r
  let p3 ← affAdd p1 r
  let m1 ← affAdd nhhh q
  let m2 ← affAdd nhhh r
  let m3 ← affAdd m1 r
  return { plus := #[hhh, p1, p2, p3], minus := #[nhhh, m1, m2, m3] }

end StandardECDSA.Phases
