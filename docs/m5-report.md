# M5 report (T17 whole-circuit assembly) — PARTIAL

## Timing

| | raw `date -u +%s` |
|---|---|
| before | `1795044773` |
| after | `1795047738` |
| **elapsed_seconds** | **2965** |

## Status: M5 is NOT complete

Proved in this round:

| theorem | file |
|---|---|
| `cmpPhase_sound` | `StandardECDSA/Main.lean` |
| `main_ops` | `StandardECDSA/Main.lean` |
| `soundness_append9` | `StandardECDSA/Main.lean` |

Not yet proved (M5 targets): `main_soundness`, `main_complete_with_seed`,
`main_completeness`, `main_accepts_iff_standard`.

## The blocking problem found and fixed this round

`ConstraintsHold.Soundness env L` is a `def`, so **every** elaboration step that
`whnf`s it also `whnf`s `L`.  For `L` containing a comparator
(`assertLtOrderOf nSubOne a`), `whnf L` unfolds `ltLoop` over the 68-run list,
and that reduction is **exponential in the number of zero runs** (the `do` block
of `ltLoop` uses `sum` twice, so each zero-run level doubles the work).  Measured
threshold: 16 runs whnf fine, 20 runs already exceeds 200 000 heartbeats, and
4 000 000 heartbeats is still not enough for 68 runs.

Consequences observed (all reproduced in a scratch file):

* `example ... := hc` (term mode) fails with `timeout at whnf`;
* `exact hc` fails; `by assumption` succeeds (no `whnf`);
* applying `assertLtOrderOf_sound nSubOne ... h` fails at `h`;
* `soundness_append3 hc` fails at `hc`.

### Fix

`boundRunsOf` now dispatches on the two bounds the circuit actually uses and
returns **sealed literal run lists** `nSubOneRuns` / `pnRuns`
(`@[irreducible]`, 68 runs each, 34 zero runs each — matching the plan's
"34 maximal zero runs" count).  With the run list irreducible, `whnf` of the
comparator circuit is stuck and therefore cheap, while the kernel still reduces
it for `rfl`/`decide` under `with_unfolding_all`.

Two `decide` proofs in `Gadgets/Cost.lean` had to become
`with_unfolding_all decide` because plain `decide` respects the irreducibility
hint.

Also changed: `assertLtOrderOf_sound` / `assertLtOrderGuardedOf_sound` now take
`hrows` immediately after the offset (before `hbool`/`hpref`/`hcover`), so the
bound can stay a metavariable while the hypothesis is checked.  Call sites in
`Gadgets/LtExplicit.lean` were updated.

## Checks

```
$ lake build StandardECDSA.Main
Build completed successfully (9020 jobs).

$ lake build
Build completed successfully (17893 jobs).
# only the pre-existing Challenge/Instances/ECDSA_P256_Digest/Challenge.lean sorries

$ grep -rn "sorry" StandardECDSA/
(no output, exit 1)

$ lake exe standardEcdsaCheck --count-only
Standard P-256 ECDSA circuit (6 fixed inputs)
allocations=4628 rows=4634 score=9262

$ python3 scripts/check_axioms.py
Tests/Axioms.lean: 26 roots passed the permitted-axiom audit
```

Cost is unchanged at the plan budget 4628/4634 = 9262.

## Files changed

```
 StandardECDSA/Gadgets/Cost.lean      |  6 +++--
 StandardECDSA/Gadgets/LtExplicit.lean|  4 ++--
 StandardECDSA/Gadgets/Scalar.lean    | 12 ++++++++--
 StandardECDSA/Gadgets/Semantics6.lean|  8 +++---
 StandardECDSA/Main.lean              | ~90 ++++++++++++++++++++++++++++++++
```

## Remaining M5 work (exact)

1. `main_soundness`: `rw [main_ops] at hc` then `soundness_append9 hc` gives the
   nine stage hypotheses; then apply `seedPhase_sound`, `curvePhase_sound`,
   `nonzeroPhase_sound`, `bitsPhase_sound`, `bindPhase_sound`,
   `cmpPhase_sound`, `fixedBase_spec`, `shiftedTables_spec`,
   `jointLadder_spec`.  Still needed:
   * `eval_linComb : Expression.eval env (linComb v lo len) = leSum (fun i : Fin len => Expression.eval env (v.get ⟨lo + i.val, _⟩))`
     (induction on `len`, `List.range_succ`/`List.foldl_append`, `Fin.sum_univ_castSucc`);
   * `prefVal_rev : prefVal (fun j => f (255 - j)) 256 = leNat (fun i : Fin 256 => f i)`
     (`prefVal_eq_sum` + `Finset.sum_range_reflect`);
   * scalar bridges `leNat rb = r.val`, `leNat sb = n - s.val`,
     `digestNat env eb = Digest.toNat ⟨digestLo, digestHi⟩`;
   * group algebra `ep = H + E•G` and `-ep = r•Q + t•R - H` ⇒ `E•G + r•Q + t•R = 0`,
     transported with `addE_toMathlib`/`mulG_toMathlib`/`mulP_toMathlib`;
   * `x_mod_order_iff_lift` for `R.X.val % n = r.val`;
   * `(standard_iff_signaturePoint ...).mpr`.
2. `main_complete_with_seed`, `main_completeness`, `main_accepts_iff_standard`:
   **no phase completeness lemmas exist yet** (`grep` of `StandardECDSA/Phases/`
   for `completeness`/`_complete` returns nothing).  Only gadget completeness
   exists (`assertBoolMain_completeness`, `nonzeroMain_completeness`,
   `selMain_completeness`, `muxConst4Main_completeness`,
   `affAddMain_completeness`, `affDoubleMain_completeness`,
   `elmMain_completeness`, `elmToMain_completeness`,
   `isOnCurveMain_completeness`, `pointEqualityMain_completeness`,
   `mux4Main_completeness`, `assertLtOrderOfMain_completeness`,
   `assertLtOrderGuardedOfMain_completeness`).  Building phase completeness is a
   large additional task.

## Note on `maxHeartbeats` / `maxRecDepth`

Neither was changed.  The `@[irreducible]` sealing is a definitional change, not
a budget change; it is what makes the concrete-bound comparator reasoning
tractable at the default 200 000 heartbeats.
