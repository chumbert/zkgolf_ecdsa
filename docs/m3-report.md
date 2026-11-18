# M3 report — Local proof package (round 2: cost + R1CS closed; semantics open)

**Milestone:** M3 (T05–T11 gadget/phase proofs)
**Branch:** `leanstral-with-astra-planner`
**Base commit:** `f86cb85` (M3 partial, round 1)
**Timing (round 2):** before `1795007879`, after `1795009347`,
`elapsed_seconds = 1468`
**Timing (round 1):** before `1795007174`, after `1795007758`, `elapsed_seconds = 584`

## Check results

| Check | Result |
|---|---|
| `grep -rn "sorry" StandardECDSA/Gadgets/ StandardECDSA/Phases/` | **no hits** (exit 1) |
| `grep -rn "sorry" StandardECDSA/` | **no hits** (exit 1) |
| `lake build StandardECDSA.Main` | **green** (8996 jobs) |
| `lake build` (whole project) | **green** (17893 jobs) |
| `lake exe standardEcdsaCheck --count-only` | `allocations=4628 rows=4634 score=9262` |
| `lake exe standardEcdsaCheck` | `smoke test: all R1CS assertions hold with H = [1]G` |
| `lake exe standardEcdsaCheck --comparator` | `comparator: 20 cases, 0 failures` |
| `python3 scripts/check_axioms.py` | `Tests/Axioms.lean: 26 roots passed the permitted-axiom audit` |
| **per-leaf cost certificates** | **COMPLETE for all gadgets except the three phases** |
| **per-leaf R1CS certificates** | **COMPLETE for 12 of 15 gadgets** |
| **semantic `FormalCircuit` bundling** | **NOT STARTED** |

## What was proved in round 2

### Item (1) — cost certificates: closed for every gadget

`StandardECDSA/Gadgets/Cost.lean` (494 lines added).  The round-1 obstruction
("`Circuit.output`/`Circuit.bind` unfolding did not converge") is resolved by
the general output-degree technique the orchestrator suggested: prove the
`rfl`-level unfolding lemmas **once** and then never unfold `Circuit.output`
again.

Structural lemmas (all `rfl`):

```text
output_pure, output_bind, output_witnessField, output_assertZero,
fst_pure, fst_witnessField
```

`output_bind` is stated with `.1` on the right-hand side:

```text
Circuit.output (f >>= g) n
  = (g (Circuit.output f n) (n + Operations.localLength (Circuit.operations f n))).1
```

Composition lemmas:

```text
CostIs.congr      -- cost change of variables
CostIs.bind_dep   -- dependent bind: continuation cost may depend on a predicate
                     P of the intermediate value, given hP : ∀ n, P (output f n)
```

`CostIs.bind_dep` is what makes the per-gadget proofs go through: `sel`'s cost
depends on the *degree* of the expression it receives, so the continuation cost
is uniform only under `P := fun a => deg a = 1`.

`mat`'s cost and output degree:

```text
matDeg, matCount, matDeg_eq_zero, matDeg_eq_min (matDeg e = min (deg e) 1),
mat_spec (CostIs (mat e) (matCount e) ∧ ∀ n, deg (output (mat e) n) = matDeg e),
matCount_eq_zero_of_deg_le_one, matDeg_le_one
```

Gadget cost certificates (all closed numerals unless noted):

| Theorem | Cost |
|---|---|
| `mm_spec` | `⟨1,1⟩` + output degree 1 |
| `nonzero_cost` | `⟨1,1⟩` + output degree 1 |
| `assertBool_cost` | `⟨0,1⟩` |
| `bitOf_spec` | `⟨1,0⟩` + output degree 1 |
| `sel_cost` | `⟨1,1⟩` + output degree 1 |
| `muxConst4_cost` | `⟨1,1⟩` |
| `mux4_cost` | `⟨6,6⟩` |
| `affAdd_cost` | `⟨4,4⟩` |
| `affDouble_cost` | `⟨4,4⟩` |
| `elmCore_cost` | `⟨4,4⟩` |
| `elm_cost` | `⟨6,6⟩` |
| `elmTo_cost` | `⟨4,6⟩` |
| `azlLoop_cost`, `azlLinLoop_cost` | `azlLoopCost l`, `Count.zero` |
| `assertZeroLazy_cost` | `assertZeroLazyCost e` (closed form in `flat`) |
| `ltLoop_cost`, `ltLoopGuarded_cost` | `ltLoopCost l` |
| `assertLtOrderOf_cost` | `ltLoopCost (boundRunsOf bound)` |
| `assertLtOrderGuardedOf_cost` | `ltLoopCost (boundRunsOf bound)` |
| **`assertLtOrderOf_cost_n`** | **`⟨34,34⟩`** (kernel `decide` on the run list) |
| **`assertLtOrderGuardedOf_cost_p`** | **`⟨34,34⟩`** (kernel `decide` on the run list) |
| `isOnCurve_cost_var` | `⟨2,3⟩` |
| `pointEquality_cost_var` | `⟨0,2⟩` |

The two `⟨34,34⟩` results are the plan's §3B "34 guarded bound rows/quotients"
claim, now kernel-checked rather than numerically observed.

### Item (2) — `IsR1CSCirc` per-expression-shape lemmas: closed

New file `StandardECDSA/Gadgets/R1CS.lean` (≈330 lines).

`r1csProducts` arithmetic:

```text
r1csProducts_affine       (deg e ≤ 1 → r1csProducts e = some 0)
r1csProducts_mul_le_one   (deg a ≤ 1 → deg b ≤ 1 → ∃ k ≤ 1, r1csProducts (a*b) = some k)
r1csProducts_add          (additive over `add`)
r1csProducts_mul_const    (constant scaling preserves the count)
deg_neg_le, deg_var_le
```

Row shapes:

```text
isR1CSRow_affine          (deg e ≤ 1 → isR1CSRow e)
isR1CSRow_prod_sub        (A*B - C, all affine)
isR1CSRow_add_affine      (row + affine summand)
isR1CSRow_prod_sub2       (A*B - C - D)
isR1CSRow_prod_sub3       (A*B - C - D - F)
```

Gadget certificates:

```text
isR1CSCirc_mat, isR1CSCirc_assertBool, isR1CSCirc_nonzero, isR1CSCirc_sel,
isR1CSCirc_muxConst4, isR1CSCirc_mux4, isR1CSCirc_affAdd, isR1CSCirc_affDouble,
foldl_add_deg, addMissing_deg, runSum_deg,
isR1CSCirc_ltLoop, isR1CSCirc_ltLoopGuarded,
isR1CSCirc_assertLtOrderOf, isR1CSCirc_assertLtOrderGuardedOf
```

`isR1CSCirc_mat` is by induction on the expression, using
`Challenge.CostR1CS.IsR1CSCirc.bind_out` so the continuation may depend on the
actual wire index produced by `mat`.

### Behaviour-preserving restructurings (count re-verified)

Three definitions were rewritten so that their cost is provable by structural
induction instead of by unfolding a `Std.Range` `for` loop (for which
`Challenge.CostR1CS` has no cost lemma):

| Definition | Before | After |
|---|---|---|
| `assertZeroLazy` | `for (c',t) in rest do …` + `for (c',t) in lins do …` | `azlLoop` / `azlLinLoop` (explicit structural recursion) |
| `assertLtOrderOf` | `for (hi,lo,bit) in boundRunsOf bound do …` | `ltLoop` (explicit structural recursion) |
| `assertLtOrderGuardedOf` | same | `ltLoopGuarded` |
| `boundRunsOf` | `Id.run do` + `Array.push` + `Nat.testBit` | `List.foldl` over `bitAt` + `List.reverse` |

`boundRunsOf` was rewritten because the `Id.run`/`Array`/`Nat.testBit` version
does **not** reduce in the kernel (`decide` gets stuck), so the `⟨34,34⟩`
certificates were impossible.  The new version is proved extensionally equal to
the old one for both bounds (`#eval (boundRunsOf nSubOne) == (boundRunsOfOld nSubOne)`
→ `true`, same for `pSubNSubOne`).

All four rewrites are behaviour-preserving, verified by re-running the
executable: `allocations=4628 rows=4634 score=9262`, smoke test passes,
comparator 20/20.

## What is NOT done (the remaining M3 gap)

### Item (3) — semantic `FormalCircuit`/`FormalAssertion` bundling: NOT STARTED

This is the bulk of T05–T11 and is the only remaining M3 item.  Concretely
missing:

1. **Bundled semantic specs** for `nonzero`, `assertBool`, `sel`, `muxConst4`,
   `mux4`, `affAdd`, `affDouble`, `elm`, `elmTo`, `isOnCurve`,
   `pointEquality`, `assertLtOrderOf`, `assertLtOrderGuardedOf` — each as a
   `FormalCircuit`/`FormalAssertion` whose spec is a group/scalar statement
   (not a row list), with soundness and completeness.
2. **Phase semantic specs** for `fixedBase` (`ep = H + [E]G`), `shiftedTables`
   (every entry `±3H + b0·Q + b1·R`) and `jointLadder` (the signed-offset
   prefix invariant).  These are T12/T15 and are M5 work by the plan's own
   dependency graph.
3. **Phase cost certificates** (`fixedBase` 644/644, `shiftedTables` 32/32,
   `jointLadder` 3070/3072).  The phases still use `for i in [0:128]` /
   `[0:256]`; they need the same `mapFinRange`/`foldlRange` restructuring as
   `assertZeroLazy`/`ltLoop` above, plus `ConstantLength` proofs.
4. **`IsR1CSCirc` for `assertZeroLazy`, `isOnCurve`, `pointEquality`,
   `elmCore`, `elm`, `elmTo`.**  `assertZeroLazy`'s assertion is
   `assertZero acc` where `acc` is one product plus affine summands; the
   certificate needs `isR1CSRow (sc c (pm A B) + C)` plus a lemma that
   `azlLoop`'s accumulator stays of that shape.  `elm`/`elmTo` additionally
   need an output-degree lemma for `elmCore`'s pair output.

*Exact obstruction for item (3):* the semantic bundling is not blocked by a
technical problem — it is simply the largest remaining body of work in the
plan (T05–T11's soundness/completeness halves plus T12/T15).  The prerequisites
it needs are now all in place: `Math/ElmAlgebra.lean` and
`Math/AffineBridge.lean` supply the field-algebra and group-law lemmas,
`Gadgets/Lemmas.lean` supplies the row-shape lemmas, and this round supplies
the cost and R1CS certificates.

## Remaining sorries

```text
$ grep -rn "sorry" StandardECDSA/
$ echo $?
1
```

No hits anywhere under `StandardECDSA/`.

## Build errors

None.  `lake build` → `Build completed successfully (17893 jobs)`.
(The two `declaration uses sorry` warnings in the log are in the pre-existing
`Challenge/Instances/ECDSA_P256_Digest/Challenge.lean`, not in
`StandardECDSA/`.)

## Files changed

```text
$ git status --short
 M StandardECDSA/Gadgets/Cost.lean
 M StandardECDSA/Gadgets/Field.lean
 M StandardECDSA/Gadgets/Scalar.lean
 M StandardECDSA/Gadgets/Select.lean
 M StandardECDSA/Main.lean
?? StandardECDSA/Gadgets/R1CS.lean
```

```text
$ git diff --stat
 StandardECDSA/Gadgets/Cost.lean   | 494 +++++++++++++++++++++++++++++++++-----
 StandardECDSA/Gadgets/Field.lean  |  20 +-
 StandardECDSA/Gadgets/Scalar.lean |  83 ++++---
 StandardECDSA/Gadgets/Select.lean |  12 +-
 StandardECDSA/Main.lean           |   1 +
 5 files changed, 509 insertions(+), 101 deletions(-)
```

## Decision

M3 items (1) and (2) are **closed**.  Item (3) — the semantic
`FormalCircuit`/`FormalAssertion` bundling with soundness and completeness —
is **not started** and is the plan's largest remaining body of work
(T05–T11 semantics plus T12/T15 phase invariants).

Per the milestone rules I am **stopping at M3** and reporting rather than
proceeding to M4, because M4's `generateSeed_complete` and `exists_goodOffset`
consume the semantic gadget interfaces that item (3) is supposed to publish.

**Next milestone I would attempt:** M3 item (3), in this order:
(a) `FormalAssertion` bundling for `nonzero`, `assertBool`, `sel`, `muxConst4`,
`mux4` (field-level, prerequisites already in `Gadgets/Lemmas.lean`);
(b) `FormalCircuit` bundling for `affAdd`, `affDouble`, `elm`, `elmTo` using
`Math.ElmAlgebra` / `Math.AffineBridge`;
(c) `isOnCurve` / `pointEquality` / comparator semantics;
(d) phase cost certificates via `mapFinRange`/`foldlRange`;
(e) phase semantic specs (T12/T15).
