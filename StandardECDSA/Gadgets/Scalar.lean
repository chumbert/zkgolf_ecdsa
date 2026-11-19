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

/-- The indices `255, 254, ..., 0` as a literal list, so that `boundRunsOf`
reduces cheaply in the elaborator (a literal avoids the 256-deep `List.range`). -/
def idx256 : List Nat :=
  [255, 254, 253, 252, 251, 250, 249, 248, 247, 246, 245, 244, 243, 242, 241, 240, 239, 238, 237, 236, 235, 234, 233, 232, 231, 230, 229, 228, 227, 226, 225, 224, 223, 222, 221, 220, 219, 218, 217, 216, 215, 214, 213, 212, 211, 210, 209, 208, 207, 206, 205, 204, 203, 202, 201, 200, 199, 198, 197, 196, 195, 194, 193, 192, 191, 190, 189, 188, 187, 186, 185, 184, 183, 182, 181, 180, 179, 178, 177, 176, 175, 174, 173, 172, 171, 170, 169, 168, 167, 166, 165, 164, 163, 162, 161, 160, 159, 158, 157, 156, 155, 154, 153, 152, 151, 150, 149, 148, 147, 146, 145, 144, 143, 142, 141, 140, 139, 138, 137, 136, 135, 134, 133, 132, 131, 130, 129, 128, 127, 126, 125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112, 111, 110, 109, 108, 107, 106, 105, 104, 103, 102, 101, 100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80, 79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64, 63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]

/-- The maximal runs of `n - 1`, as a literal list (68 runs, 34 of them zero
runs).  Sealed here so that the elaborator never has to reduce the generic
`boundRunsOf` computation for this concrete bound. -/
@[irreducible] def nSubOneRuns : List (Nat × Nat × Bool) :=
  [(255, 224, true), (223, 192, false), (191, 127, true), (126, 126, false), (125, 122, true), (121, 120, false), (119, 117, true), (116, 115, false), (114, 113, true), (112, 112, false), (111, 107, true), (106, 106, false), (105, 105, true), (104, 104, false), (103, 103, true), (102, 102, false), (101, 101, true), (100, 100, false), (99, 98, true), (97, 97, false), (96, 95, true), (94, 94, false), (93, 93, true), (92, 91, false), (90, 88, true), (87, 85, false), (84, 84, true), (83, 83, false), (82, 79, true), (78, 77, false), (76, 73, true), (72, 72, false), (71, 71, true), (70, 67, false), (66, 66, true), (65, 64, false), (63, 60, true), (59, 58, false), (57, 55, true), (54, 54, false), (53, 51, true), (50, 49, false), (48, 46, true), (45, 44, false), (43, 43, true), (42, 42, false), (41, 41, true), (40, 40, false), (39, 38, true), (37, 34, false), (33, 33, true), (32, 32, false), (31, 26, true), (25, 23, false), (22, 21, true), (20, 18, false), (17, 16, true), (15, 14, false), (13, 13, true), (12, 11, false), (10, 10, true), (9, 9, false), (8, 8, true), (7, 7, false), (6, 6, true), (5, 5, false), (4, 4, true), (3, 0, false)]

/-- The maximal runs of `(p - n) - 1`, as a literal list (68 runs, 34 of them
zero runs). -/
@[irreducible] def pnRuns : List (Nat × Nat × Bool) :=
  [(255, 127, false), (126, 126, true), (125, 122, false), (121, 120, true), (119, 117, false), (116, 115, true), (114, 113, false), (112, 112, true), (111, 107, false), (106, 106, true), (105, 105, false), (104, 104, true), (103, 103, false), (102, 102, true), (101, 101, false), (100, 100, true), (99, 98, false), (97, 96, true), (95, 95, false), (94, 94, true), (93, 93, false), (92, 91, true), (90, 88, false), (87, 85, true), (84, 84, false), (83, 83, true), (82, 79, false), (78, 77, true), (76, 73, false), (72, 72, true), (71, 71, false), (70, 67, true), (66, 66, false), (65, 64, true), (63, 60, false), (59, 58, true), (57, 55, false), (54, 54, true), (53, 51, false), (50, 49, true), (48, 46, false), (45, 44, true), (43, 43, false), (42, 42, true), (41, 41, false), (40, 40, true), (39, 38, false), (37, 34, true), (33, 33, false), (32, 32, true), (31, 26, false), (25, 23, true), (22, 21, false), (20, 18, true), (17, 16, false), (15, 14, true), (13, 13, false), (12, 11, true), (10, 10, false), (9, 9, true), (8, 8, false), (7, 7, true), (6, 6, false), (5, 5, true), (4, 4, false), (3, 2, true), (1, 1, false), (0, 0, true)]

/-- Maximal runs of equal bits of the inclusive bound `bound`, most significant
first, as `(hi, lo, bit)` with `hi ≥ lo`.  The two bounds used by the circuit are
sealed as literal lists so that the elaborator can reduce `boundRunsOf` cheaply;
the generic branch is kept for the abstract specification. -/
def boundRunsOf (bound : Nat) : List (Nat × Nat × Bool) :=
  if bound = Challenge.Specs.ECDSAP256.n - 1 then nSubOneRuns
  else if bound = Challenge.Specs.ECDSAP256.p - Challenge.Specs.ECDSAP256.n - 1 then pnRuns
  else
    (idx256.foldl
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
