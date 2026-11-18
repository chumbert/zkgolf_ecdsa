/-
# ELM gadget: `2P + Q` with a redundant second denominator

Ported from the pinned `circuit_baseline` revision
(`3a1bd20749ae0b6400a158651dba64a2c5fc58ff`), `Baseline/Projected/Offset.lean`
(`elmCore`, `elm`, `elmTo`).

The ELM step computes `2P + Q` as `(P + Q) + P` sharing the intermediate
`x`-coordinate.  The first denominator `Q.x - P.x` is guarded by an explicit
inverse row; the second denominator `P.x - xu` is *implied* by the curve
equations and the first three rows (`Math/OffsetConditions.lean`,
`elm_second_denominator_ne`), so no extra guard row is allocated.

Costs: `elm` 6 allocations / 6 rows, `elmTo` 4 allocations / 6 rows.

Task T09.
-/

import StandardECDSA.Gadgets.Affine

namespace StandardECDSA.Gadgets

/-- ELM prefix: returns `(xu, l2)` where `xu` is the `x`-coordinate of `P + Q`
and `l2` the slope of the second addition.  The first denominator is guarded;
the second is implied by the curve equations and the first three rows. -/
def elmCore (p q : Pt) : C Pt := do
  let inv1 ← nonzero (q.1 - p.1)
  let l1 ← Circuit.witnessField (.mul (.expr (q.2 - p.2)) (.expr inv1))
  Circuit.assertZero (pm (q.1 - p.1) l1 - (q.2 - p.2))
  let xu ← Circuit.witnessField (.add (.mul (.expr l1) (.expr l1)) (.expr (-p.1 - q.1)))
  Circuit.assertZero (pm l1 l1 - p.1 - q.1 - xu)
  let l2 ← Circuit.witnessField (.add (.mul (.expr (sc 2 p.2)) (.inv (.expr (p.1 - xu)))) (.expr (-l1)))
  Circuit.assertZero (pm (l1 + l2) (p.1 - xu) - sc 2 p.2)
  pure (xu, l2)

/-- `2P + Q` with the intermediate `y` coordinate omitted.  6 allocations, 6 rows. -/
def elm (p q : Pt) : C Pt := do
  let (xu, l2) ← elmCore p q
  let x ← Circuit.witnessField (.add (.mul (.expr l2) (.expr l2)) (.expr (-p.1 - xu)))
  Circuit.assertZero (pm l2 l2 - p.1 - xu - x)
  let y ← Circuit.witnessField (.add (.mul (.expr l2) (.expr (p.1 - x))) (.expr (-p.2)))
  Circuit.assertZero (pm l2 (p.1 - x) - p.2 - y)
  pure (x, y)

/-- Final step: assert `2P + Q = target` against an already supplied target, so
no replacement output coordinates are allocated.  4 allocations, 6 rows. -/
def elmTo (p q target : Pt) : C Unit := do
  let (xu, l2) ← elmCore p q
  Circuit.assertZero (pm l2 l2 - p.1 - xu - target.1)
  Circuit.assertZero (pm l2 (p.1 - target.1) - p.2 - target.2)

end StandardECDSA.Gadgets
