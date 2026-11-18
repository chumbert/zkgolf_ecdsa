/-
# Affine addition and doubling gadgets

Ported from the pinned `circuit_baseline` revision
(`3a1bd20749ae0b6400a158651dba64a2c5fc58ff`), `Baseline/Projected/Offset.lean`
(`affAdd`, `affDouble`).  Both cost 4 allocations and 4 rows.

`affAdd p q` requires `q.x ≠ p.x`; the guard is the explicit inverse row of
`nonzero (q.1 - p.1)`, so soundness derives the distinct-`x` condition from the
constraints rather than assuming it.  `affDouble p` has no separate inverse row:
the slope row together with nonsingularity implies `2·y ≠ 0`
(`Math/OffsetConditions.lean`, `double_denominator_ne`).

Task T08.
-/

import StandardECDSA.Gadgets.Field

namespace StandardECDSA.Gadgets

/-- Affine addition with an explicit distinct-`x` guard.  4 allocations, 4 rows. -/
def affAdd (p q : Pt) : C Pt := do
  let inv ← nonzero (q.1 - p.1)
  let l ← Circuit.witnessField (.mul (.expr (q.2 - p.2)) (.expr inv))
  Circuit.assertZero (pm (q.1 - p.1) l - (q.2 - p.2))
  let x ← Circuit.witnessField (.add (.mul (.expr l) (.expr l)) (.expr (-p.1 - q.1)))
  Circuit.assertZero (pm l l - p.1 - q.1 - x)
  let y ← Circuit.witnessField (.add (.mul (.expr l) (.expr (p.1 - x))) (.expr (-p.2)))
  Circuit.assertZero (pm l (p.1 - x) - p.2 - y)
  pure (x, y)

/-- Affine doubling.  4 allocations, 4 rows.  The slope row and nonsingularity
imply `2·y ≠ 0`, so no extra inverse row is needed. -/
def affDouble (p : Pt) : C Pt := do
  let xx ← mm p.1 p.1
  let l ← Circuit.witnessField (.mul (.expr (sc 3 xx + cst pa)) (.inv (.expr (sc 2 p.2))))
  Circuit.assertZero (pm (sc 2 p.2) l - sc 3 xx - cst pa)
  let x ← Circuit.witnessField (.add (.mul (.expr l) (.expr l)) (.expr (-sc 2 p.1)))
  Circuit.assertZero (pm l l - sc 2 p.1 - x)
  let y ← Circuit.witnessField (.add (.mul (.expr l) (.expr (p.1 - x))) (.expr (-p.2)))
  Circuit.assertZero (pm l (p.1 - x) - p.2 - y)
  pure (x, y)

/-- Negation of an affine point. -/
def negPt (p : Pt) : Pt := (p.1, -p.2)

end StandardECDSA.Gadgets
