# M2 report — Standard circuit runs

**Milestone:** M2 (T05 field gadgets, T07 scalar circuit, T10 muxes, T11 fixed
tables, T12 fixed-base/shifted tables)
**Branch:** `leanstral-with-astra-planner`
**Base commit:** `ad51345` (M1)
**Timing:** before `1795005930`, after `1795007149`, `elapsed_seconds = 1219`

> Timing note: the M2 "before" stamp is the M1 "after" stamp, i.e. the moment
> M2 investigation began.  No separate `date -u +%s` was taken at that instant
> (same protocol deviation as M0, documented in the M1 report).

## Check results

| Check | Result |
|---|---|
| `lake build StandardECDSA.Main` | **green** (8991 jobs) |
| `lake build` (whole project) | **green** (17893 jobs) |
| `lake build standardEcdsaCheck` | **green** (17971 jobs) |
| `lake exe standardEcdsaCheck --count-only` | `allocations=4628 rows=4634 score=9262` |
| `grep -rn "sorry" StandardECDSA/` | **no hits** (exit 1) |
| `lake exe standardEcdsaCheck` (witness smoke test) | all 4634 R1CS assertions hold |
| `lake exe standardEcdsaCheck --comparator` | 20 cases, 0 failures |

### Measured cost vs. the plan's proposed budget

```text
allocations=4628 rows=4634 score=9262
```

The plan proposed **9,262 = 4,628 allocations + 4,634 rows**.  The measured
count is **exactly** the proposed budget — delta `0 / 0 / 0`.

The independent phase ledger of plan §3 also matches exactly:

| Phase | Ledger alloc/rows | Measured alloc/rows |
|---|---|---|
| Seed hints: `ry`, `Hx`, `Hy`, `overflow`, 768 scalar bits | 772 / 0 | 772 / 0 |
| On-curve `Q`, `R`, `H` | 6 / 9 | 6 / 9 |
| Nonzero `r` and `t` | 2 / 2 | 2 / 2 |
| Boolean scalar bits and `overflow` | 0 / 769 | 0 / 769 |
| Two digest and two scalar bindings | 0 / 4 | 0 / 4 |
| Three 34-run comparators | 102 / 102 | 102 / 102 |
| Fixed-base initial addition + 128 mux/add windows | 644 / 644 | 644 / 644 |
| Compute `2H` and `3H` | 8 / 8 | 8 / 8 |
| Six shifted-table additions | 24 / 24 | 24 / 24 |
| 255 mux/ELM steps + final mux/ELM-to-target | 3,070 / 3,072 | 3,070 / 3,072 |
| **Total** | **4,628 / 4,634** | **4,628 / 4,634** |

## What was built

New modules (all new files, no `sorry`, no new axioms):

| File | Contents |
|---|---|
| `StandardECDSA/Gadgets/Field.lean` | `Fp`, `E`, `C`, `Pt`, `deg`, `cst`, `sc`, `constVal`, `mat`, `mm`, `pm`, `flat`, `isProd`, `assertZeroLazy`, curve constants `pa/pb/k3b/gx/gy`, `isOnCurve`, `pointEquality`, `nonzero` |
| `StandardECDSA/Gadgets/Select.lean` | `bitOf`, `assertBool`, `sel`, `mux8`, `muxConst4`, `mux4` |
| `StandardECDSA/Gadgets/Scalar.lean` | `boundRunsOf`, `assertLtOrderOf`, `assertLtOrderGuardedOf`, `nFp`, `pSubNSubOne`, `nSubOne` |
| `StandardECDSA/Gadgets/Affine.lean` | `affAdd` (4/4), `affDouble` (4/4), `negPt` |
| `StandardECDSA/Gadgets/ELM.lean` | `elmCore`, `elm` (6/6), `elmTo` (4/6) |
| `StandardECDSA/Math/FixedTables.lean` | `KP`, `affine`, `gPoint`, `mulG`, `fixedTables` (128×4), `fixedShift` |
| `StandardECDSA/Phases/FixedBase.lean` | `fixedBase` (644/644) |
| `StandardECDSA/Phases/ShiftedTables.lean` | `Tables`, `shiftedTables` (32/32) |
| `StandardECDSA/Phases/JointLadder.lean` | `jointLadder` (3,070/3,072) |
| `StandardECDSA/Main.lean` | rewritten: `hintKey`, `hint`, `nFp`, `main` (the assembled six-input circuit) |
| `StandardECDSA/Check.lean` | `inputVar`, `operations`, `count`, `hintProvider`, `verifyPoint`, `seedOf`, `firstFailure`, `searchH`, `testVector`, `comparatorOk`, `comparatorReport`, `run`, `main` |
| `lakefile.lean` | added `lean_exe standardEcdsaCheck` (root `StandardECDSA.Check`) |

## Plan §3 modifications, as implemented

* **A. Only the shifted tables.**  `originalTable` (8 hints + 4 `addE` + 4
  `pointEquality`) is deleted.  `shiftedTables` builds, for each sign
  `ε ∈ {+1,-1}`, `P0 = [3ε]H`, `P1 = P0+Q`, `P2 = P0+R`, `P3 = P1+R`, using six
  ordinary `affAdd`.  It never asks for affine coordinates of unshifted `Q+R`,
  so it works when `Q+R = O` or `Q = R`.
* **B. `overflow` branch.**  One Boolean `overflow` (seed cell 3), `R.x` is the
  affine expression `rx = r + n·overflow`, and
  `assertLtOrderGuardedOf (p-n-1) overflow rBits` imposes
  `(missingOnes + (1-overflow)) · quotient = runSum` per zero run — one product
  per row, never cubic.  `(p-n)-1 = 0x4319055358e8617b0c46353d039cdaad` has 34
  maximal zero runs (kernel-checked in `Math/ConstantBounds.lean`).
* **C. Full digest binding.**  `Σ_{i<128} 2^i eBit[i] = digestLo` and
  `Σ_{i<128} 2^i eBit[128+i] = digestHi` — two rows instead of one.
* **D. Scalar checks retained.**  Boolean `r`/`t` bits, `rBits < n`,
  `tBits < n`, nonzero `r` and `t = n-s`; `tBits` recomposed to the field
  expression `n-s`.  The `pkX` inverse requirement is removed.

## Validation beyond the gate

* **Generated-witness smoke test.**  `lake exe standardEcdsaCheck` builds a
  standard-valid signature (`d = 12345`, `k = 67890`,
  `E = 0x1234…cdef`), computes `V = [u₁]G + [u₂]Q`, derives the honest seed
  (`ry = y(V)`, `overflow = 0`, 768 scalar bits), runs
  `FlatOperation.witgen` and evaluates every assertion.  Result:
  `smoke test: all R1CS assertions hold with H = [1]G`.
* **Gated-comparator unit test.**  `lake exe standardEcdsaCheck --comparator`
  simulates the comparator rows on concrete bit vectors with exactly the
  witness the circuit computes.  It confirms (i) the ordinary comparator is
  sound *and* complete for `a ≤ n-1` at `v ∈ {0,1,2,n-2,n-1,n,n+1,2^256-1}`,
  (ii) the guarded comparator with `guard = 1` behaves identically for bound
  `p-n-1`, and (iii) with `guard = 0` it is satisfiable for every tested `v`
  including `2^256-1`.  `comparator: 20 cases, 0 failures`.

## Two transcription bugs found and fixed during M2

Both were in the ported witness expressions (the *rows* were correct, so the
count was unaffected):

1. `Gadgets/Affine.lean`, `affDouble`: the slope witness must be
   `(3x²+a) · (2y)⁻¹`, not `(3x²+a) · (2y)`.
2. `Gadgets/ELM.lean`, `elmCore`: the second slope witness must be
   `2y · (p.x - xu)⁻¹ - l₁`, not `2y · (p.x - xu) - l₁`.

Both were caught by the smoke test (first failing rows 1531 and 1571
respectively) and are now fixed.

## Remaining sorries

```text
$ grep -rn "sorry" StandardECDSA/
$ echo $?
1
```

No hits.

## Build errors

None.  `lake build` completes with `Build completed successfully (17893 jobs)`.

## Files changed

```text
$ git status --short
 M StandardECDSA/Main.lean
 M lakefile.lean
?? StandardECDSA/Check.lean
?? StandardECDSA/Gadgets/
?? StandardECDSA/Math/FixedTables.lean
?? StandardECDSA/Phases/

$ git diff --stat
 StandardECDSA/Main.lean | 156 +++++++++++++++++++++++++++++++++++-------------
 lakefile.lean           |   3 +
 2 files changed, 119 insertions(+), 40 deletions(-)
```

## Notes for M3

* The circuit is *unproved*: `Gadgets/` and `Phases/` contain definitions only.
  M3 must add the bundled `FormalCircuit`/`FormalAssertion` boundaries and the
  per-leaf cost/R1CS certificates.
* `mux8` and `pointEquality` are ported for reference but are **not** used by
  the standard circuit; they cost nothing.
* The `overflow = 1` branch has probability `(p-n)/p ≈ 2^-129`
  (`p - n = 0x4319055358e8617b0c46353d039cdaae`, 127 bits), so it cannot be
  exercised by random signing.  T19 must construct it via
  `Q = [r⁻¹]([s]R - [E]G)` for a finite `R` with `n ≤ x(R) < p`; finding such
  an `R` is itself a ~2^129 search, so T19 should instead certify the branch
  at the row level (as `--comparator` already does) and document the
  infeasibility of an end-to-end fixture.
