/-
# Scalar gadgets for the standard P-256 ECDSA circuit

Ported from the pinned `circuit_baseline` revision
(`3a1bd20749ae0b6400a158651dba64a2c5fc58ff`), `Baseline/Optimized.lean`
(`boundRuns`, `assertLtOrder`), extended with the *guarded* comparator required
by the standard circuit's `overflow` branch (plan §3B).

## The comparator

`assertLtOrderOf bound a` asserts `a ≤ bound` for a Boolean bit vector `a`
(least-significant bit first), where `bound` is a compile-time constant.

`missing` counts the missing ONE bits of `bound` in the prefix already scanned.
For each maximal ZERO run of `bound` with bit-sum `sum`, the gadget imposes

```text
missing * quotient = sum
```

If `missing = 0` the whole zero run is forced to zero; otherwise the input
already has a smaller preceding bit and a quotient exists for any `sum`.  Both
sums count at most 256 Boolean bits, so zero cannot arise by field wraparound.
One allocation and one R1CS row per zero run; no equality flags are needed.

## The guarded comparator

`assertLtOrderGuardedOf bound guard a` asserts `guard = 1 → a ≤ bound` by
imposing, for each maximal ZERO run,

```text
(missing + (1 - guard)) * quotient = sum
```

When `guard = 1` this is the ordinary comparison.  When `guard = 0` the first
factor is a positive integer at most 257, so a quotient exists for every Boolean
bit vector.  It remains one product per row; multiplying an existing quadratic
assertion by `guard` would instead make it cubic.

Both `n - 1` and `(p - n) - 1` have 34 maximal zero runs
(`Math/ConstantBounds.lean`), so the three comparators cost 102 allocations and
102 rows.

Task T06 (mathematics) / T07 (circuit).
-/

import StandardECDSA.Gadgets.Select
import StandardECDSA.Math.ConstantBounds

namespace StandardECDSA.Gadgets

/-- Maximal runs of equal bits of the inclusive bound `bound`, most significant
first, as `(hi, lo, bit)` with `hi ≥ lo`.  Written with `bitAt` and `foldl` so
that it reduces in the kernel for concrete bounds. -/
def boundRunsOf (bound : Nat) : List (Nat × Nat × Bool) :=
  ((List.range 256).reverse.foldl
    (fun acc k =>
      let b := StandardECDSA.Math.bitAt bound k
      match acc with
      | (hi, _, b') :: rest => if b == b' then (hi, k, b') :: rest else (k, k, b) :: acc
      | [] => [(k, k, b)])
    []).reverse

/-- Add the missing ONE bits of the run `[lo, hi]` to `m`. -/
def addMissing (a : Nat → E) (hi lo : Nat) (m : E) : E :=
  (List.range (hi - lo + 1)).foldl (fun m j => m + (cst 1 - a (hi - j))) m

/-- Sum of the bits of the run `[lo, hi]`. -/
def runSum (a : Nat → E) (hi lo : Nat) : E :=
  (List.range (hi - lo + 1)).foldl (fun s j => s + a (hi - j)) (cst 0)

/-- The comparison loop: one allocation and one row per maximal zero run. -/
def ltLoop (a : Nat → E) (missing : E) : List (Nat × Nat × Bool) → C Unit
  | [] => pure ()
  | (hi, lo, bit) :: rest =>
      if bit then ltLoop a (addMissing a hi lo missing) rest
      else do
        let sum := runSum a hi lo
        let quotient ← Circuit.witnessField (.mul (.expr sum) (.inv (.expr missing)))
        Circuit.assertZero (pm missing quotient - sum)
        ltLoop a missing rest

/-- The guarded comparison loop: the first factor is `missing + (1 - guard)`. -/
def ltLoopGuarded (a : Nat → E) (guard : E) (missing : E) :
    List (Nat × Nat × Bool) → C Unit
  | [] => pure ()
  | (hi, lo, bit) :: rest =>
      if bit then ltLoopGuarded a guard (addMissing a hi lo missing) rest
      else do
        let sum := runSum a hi lo
        let factor := missing + (cst 1 - guard)
        let quotient ← Circuit.witnessField (.mul (.expr sum) (.inv (.expr factor)))
        Circuit.assertZero (pm factor quotient - sum)
        ltLoopGuarded a guard missing rest

/-- Assert `a ≤ bound`, given Boolean affine bits `a` (LSB first). -/
def assertLtOrderOf (bound : Nat) (a : Nat → E) : C Unit :=
  ltLoop a (cst 0) (boundRunsOf bound)

/-- Assert `guard = 1 → a ≤ bound`, given Boolean affine bits `a` (LSB first)
and a Boolean `guard`.  One allocation and one row per zero run of `bound`. -/
def assertLtOrderGuardedOf (bound : Nat) (guard : E) (a : Nat → E) : C Unit :=
  ltLoopGuarded a guard (cst 0) (boundRunsOf bound)

/-- The P-256 group order as a field element. -/
def nFp : Fp := (Challenge.Specs.ECDSAP256.n : Fp)

/-- `(p - n) - 1`, the inclusive bound for the `overflow` branch. -/
def pSubNSubOne : Nat := Challenge.Specs.ECDSAP256.p - Challenge.Specs.ECDSAP256.n - 1

/-- `n - 1`, the inclusive bound for the signature scalars. -/
def nSubOne : Nat := Challenge.Specs.ECDSAP256.n - 1

end StandardECDSA.Gadgets
