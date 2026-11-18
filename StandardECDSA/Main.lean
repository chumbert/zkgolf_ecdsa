/-
# Standard P-256 ECDSA circuit and proofs

This module assembles the standard P-256 ECDSA circuit and its correctness
proofs.

## Status

**M1 (correct target) is complete for the mathematical foundation.**  The
following are proved, with no `sorry` and no axioms beyond `propext`,
`Classical.choice` and `Quot.sound`:

* `Math.P256` — the P-256 field is prime, the generator is on the curve, the
  curve is nonsingular, the cubic `x³ + a·x + b` has no root in `F_p` (no
  rational two-torsion), and the arithmetic inequalities `n < p < 2n`,
  `2p + 1 < 3n`, `n < 2^256`.
* `Math.GroupOrder` — `n` is prime (kernel-checked Pratt certificate),
  `[n]G = O`, `addOrderOf G = n`, `n ∣ #E`, `#E ≤ 2p + 1`, `#E` odd, hence
  `#E = n`; consequently `[n]P = O` for every curve point and multiplication by
  `k` with `0 < k < n` is injective.  **No subgroup, cardinality or curve-order
  hypothesis remains.**
* `Math.ScalarEncoding` — `bitsToNat`/`natToBits` round trips, little-endian bit
  sums and their bound `leNat v < 2^k`, the field/natural bridge
  `val_leSum`, and the digest-limb bound.
* `Math.ConstantBounds` — the actual maximal zero-run lists of `n - 1` and
  `(p - n) - 1`, kernel-checked, confirming the plan's count of 34 runs each.
* `Math.OffsetConditions` — the generic ELM algebra identities, the finite
  exception counting theorem, the same-`x`-implies-equal-or-negative fact, and
  the `GoodOffset` predicate defined from group points.
* `Witness.Seed` — the typed 772-field seed layout and its admissibility
  predicate.
* `HintCausality` — the fixed-hint causality contract, stated truthfully (it is
  *not* the old `Circuit.ComputableWitnesses` obligation).
* `Interface` — the six-input interface and the prover/verifier contracts.

## Not yet done

The circuit itself (`Gadgets/`, `Phases/`, `Main`), the 1,039-slot enumeration
and coverage theorem (T13), the concrete safe-offset existence (T14), the
signature-equation equivalence (T03), witness generation (T16) and the
end-to-end theorems are milestones M2–M6 and are not part of this module yet.
-/

import StandardECDSA.Interface
import StandardECDSA.Spec
import StandardECDSA.HintCausality
import StandardECDSA.Math.P256
import StandardECDSA.Math.GroupOrder
import StandardECDSA.Math.ScalarEncoding
import StandardECDSA.Math.ConstantBounds
import StandardECDSA.Math.OffsetConditions
import StandardECDSA.Witness.Seed

namespace StandardECDSA

end StandardECDSA
