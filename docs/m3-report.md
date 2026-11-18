# M3 report — Local proof package (PARTIAL)

**Milestone:** M3 (T05–T11 gadget/phase proofs)
**Branch:** `leanstral-with-astra-planner`
**Base commit:** `3f4aa50` (M2)
**Timing:** before `1795007174`, after `1795007758`, `elapsed_seconds = 584`

## Check results

| Check | Result |
|---|---|
| `grep -rn "sorry" StandardECDSA/Gadgets/ StandardECDSA/Phases/` | **no hits** (exit 1) |
| `grep -rn "sorry" StandardECDSA/` | **no hits** (exit 1) |
| `lake build StandardECDSA.Main` | **green** |
| `lake build` (whole project) | **green** (17893 jobs) |
| `lake exe standardEcdsaCheck` | `allocations=4628 rows=4634 score=9262`; smoke test passes |
| `python3 scripts/check_axioms.py` | 26 roots passed the permitted-axiom audit |
| **per-leaf cost/R1CS certificates** | **PARTIAL — see below** |

## What was proved

### Vendored field/group algebra (new, kernel-checked)

| File | Contents |
|---|---|
| `StandardECDSA/Math/ElmAlgebra.lean` | `elmMiddleY`, `elm_second_slope`, `elm_two_additions`, `alternating_offset_step`, `elm_second_denominator_ne`, `affine_add_onCurve`, `double_denominator_ne`, `elm_output_onCurve`, `affine_double_onCurve`, `unified_affine_add_onCurve` |
| `StandardECDSA/Math/AffineBridge.lean` | `affine_add_eq_group`, `affine_double_eq_group`, `short_nonsingular`, `elm_eq_group` |

Vendored from the pinned `circuit_baseline` revision
(`3a1bd20749ae0b6400a158651dba64a2c5fc58ff`), `Baseline/Projected/Algebra.lean`
and `Baseline/Projected/AffineBridge.lean`, with namespaces renamed to
`StandardECDSA.Math.ElmAlgebra` / `StandardECDSA.Math.AffineBridge`.  These are
exactly the field-algebra and Mathlib-group-law lemmas that the affine, doubling
and ELM gadget soundness proofs reduce to.

### Field-level gadget semantics (new, kernel-checked)

`StandardECDSA/Gadgets/Lemmas.lean`:

* `bool_iff`, `bool_iff'`, `exists_bool_of_bit` — Booleanity;
* `nonzero_spec` — the nonzero row forces `x ≠ 0`;
* `sel_spec`, `muxConst4_spec`, `mux4_spec`, `mux8_spec` — selection semantics
  for all four muxes, including the shared bit product of `muxConst4` and the
  `b0 + 2·b1` index of `mux4`;
* `affAdd_rows`, `affDouble_rows`, `elm_rows` — the gadget rows in the exact
  shape consumed by `Math.ElmAlgebra` / `Math.AffineBridge`.

### Cost certificates (new, kernel-checked)

`StandardECDSA/Gadgets/Cost.lean`:

* `matDeg`, `matCount`, `matDeg_eq_zero`, `mat_cost` — the hard case: `mat`'s
  allocation/row count as a pure function of the expression's structure;
* `matCount_eq_zero_of_deg_le_one` — `mat` is free on affine expressions;
* `mm_cost_of_affine` — `mm a b` costs `⟨1,1⟩` for affine non-constant factors;
* `nonzero_cost` (`⟨1,1⟩`), `assertBool_cost` (`⟨0,1⟩`), `bitOf_cost`
  (`⟨1,0⟩`), `sel_cost_of_affine` (`⟨1,1⟩`).

## What is NOT done (the M3 gap)

The M3 gate asks for **per-leaf cost/R1CS certificates** and for T05–T11's
gadget/phase proofs.  The following are **not** yet proved:

1. **Remaining cost certificates.**  `muxConst4`, `mux4`, `affAdd`,
   `affDouble`, `elmCore`, `elm`, `elmTo`, `isOnCurve`, `pointEquality`,
   `assertZeroLazy`, `assertLtOrderOf`, `assertLtOrderGuardedOf`, and all three
   phases (`fixedBase`, `shiftedTables`, `jointLadder`).
   *Exact obstruction:* each of these needs the **output-degree** lemma
   `deg ((g …).output n) = 1` for the sub-gadget `g` it composes (`sel`, `mm`,
   `nonzero`), because the next gadget's cost depends on the degree of the
   expression it receives.  The technique is the same as `matDeg` (a paired
   induction carrying `CostIs` and the output degree), but it must be done for
   `mat` first — `mat_spec`'s output-degree half was dropped from this commit
   because the `Circuit.output`/`Circuit.bind` unfolding did not converge
   within the time budget.  The phase costs additionally need a
   `for i in [0:128]` / `[0:256]` loop-cost lemma; `Challenge.CostR1CS`
   provides `CostIs.forEach`/`mapFinRange`/`foldlRange` for `Vector`/`Fin`
   loops only, not for `Std.Range` `for` loops.
2. **`IsR1CSCirc` certificates.**  `isR1CSRow e` is a `Prop` about the
   *structure* of `e`, so each gadget needs a per-expression-shape lemma
   (`isR1CSRow (pm a b - c)` given `deg a = deg b = 1`, etc.).  Not started.
3. **Semantic `FormalCircuit`/`FormalAssertion` bundling and
   soundness/completeness proofs.**  This is the bulk of T05–T11 and is not
   started.  The vendored `Math.ElmAlgebra` / `Math.AffineBridge` lemmas and
   the `Gadgets/Lemmas.lean` row lemmas are the prerequisites for it.

## A change made to `mat` (behaviour-preserving)

`Gadgets/Field.lean`'s `mat` now branches on the **input** degrees
`deg a = 0 ∨ deg b = 0` rather than on the degrees of the already-materialised
factors `deg a' = 0 ∨ deg b' = 0`.  This is the same branch: `mat` maps degree
`0` to degree `0` and degree `≥ 1` to degree `≥ 1`, which is exactly
`matDeg_eq_zero`.  Writing it on the inputs makes the allocation count a pure
function of the expression's structure, which is what `mat_cost` needs.

Verified behaviour-preserving: the measured cost is unchanged
(`allocations=4628 rows=4634 score=9262`) and the generated-witness smoke test
still reports `all R1CS assertions hold with H = [1]G`.

## Remaining sorries

```text
$ grep -rn "sorry" StandardECDSA/Gadgets/ StandardECDSA/Phases/
$ echo $?
1
$ grep -rn "sorry" StandardECDSA/
$ echo $?
1
```

No hits anywhere under `StandardECDSA/`.

## Build errors

None.  `lake build` completes with `Build completed successfully (17893 jobs)`.

## Files changed

```text
$ git status --short
 M StandardECDSA/Main.lean
?? StandardECDSA/Gadgets/Cost.lean
?? StandardECDSA/Gadgets/Lemmas.lean
?? StandardECDSA/Math/AffineBridge.lean
?? StandardECDSA/Math/ElmAlgebra.lean
```

## Decision

M3 is **not** complete: the cost/R1CS certificate package is partial and the
semantic gadget/phase proofs are not started.  Per the milestone rules I am
**stopping at M3** rather than proceeding to M4, because M4 (complete prover:
`exists_goodOffset`, `generateSeed_complete`) depends on M3's semantic
soundness/completeness interfaces.

**Next milestone I would attempt:** M3 continued — specifically, in order:
(a) the output-degree half of `mat_spec`; (b) the remaining gadget cost
certificates; (c) `IsR1CSCirc` per-shape lemmas; (d) the `Std.Range` loop-cost
lemma; (e) the semantic `FormalCircuit` bundling for `nonzero`, `assertBool`,
`sel`, `muxConst4`, `mux4`, `affAdd`, `affDouble`, `elm`, `elmTo`.
