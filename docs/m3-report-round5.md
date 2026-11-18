# M3 report — round 5 (item (3)(2): `assertZeroLazy` restructure + `isOnCurve`/`pointEquality` bundling)

Timing: before `1795018308`, after `1795021847`, elapsed_seconds = **3539**.

## What was done

### 1. `ExplicitCircuit (assertZeroLazy e)` for opaque `e` — unblocked

`assertZeroLazy` was **not** restructured.  Instead the offset dependence was
removed from the *elaboration* side:

* `StandardECDSA/Gadgets/AzlExplicit.lean` — added `azlLen` (an offset-free
  mirror of the wire count), `azlLoop_localLength`, `azl_localLength_eq`, and
  changed `azlExplicit`'s `localLength` from
  `fun n => Operations.localLength ((assertZeroLazy e) n).2` to the constant
  `fun _ => azlLen e`, with `localLength_eq := azl_localLength_eq e`.
  This is what `ExplicitCircuits.IsElaborated` requires (offset independence).

* `StandardECDSA/Gadgets/VarShape.lean` (new, 153 lines) — `VarEq`, a
  variable-index-irrelevance relation on expressions, with
  `refl/deg_eq/matLen_eq/constVal_eq/isProd_eq/forall₂_append/flat_eq`,
  `sum_map_matLen_eq`, `forall₂_filter`, `azlLenList`, `azlLen_eq_azlLenList`,
  `azlLenList_eq`, `azlLen_eq`, `matOut_varEq`.  Needed because `azlLen` is
  genuinely stuck on opaque `e` (it matches on `(flat 1 e).filter isProd`).

* `StandardECDSA/Gadgets/CurveExplicit.lean` (new, 112 lines) —
  `isOnCurveExpr_varEq`, `isOnCurveExplicit`, `pointEqualityExpr₁_varEq`,
  `pointEqualityExpr₂_varEq`, `pointEqualityExplicit`, `isOnCurveMain`,
  `isOnCurveFamily`, `pointEqualityMain`, `pointEqualityFamily`, the
  `ExplicitCircuits.IsElaborated` instances, and
  `ElaboratedCircuit Fp (fields 2) unit isOnCurveMain` /
  `ElaboratedCircuit Fp (fields 5) unit pointEqualityMain` via
  `ElaboratedCircuit.fromExplicit`.

### 2. `StandardECDSA/Gadgets/Semantics4.lean` (new, 943 lines)

Structural / channel lemmas:

* `forAllNoOffset_constraints` — `forAllNoOffset` + subcircuit-freeness gives
  vanishing of every `Operations.constraints` row (bridges the `shallow` vs
  full `constraints` gap in Clean).
* `forAllNoOffset_true`, `forAllNoOffset_mono` — triviality and pointwise
  monotonicity of `forAllNoOffset`.
* `requirements_of_nil`, `inChannelsOrRequirements_nil` — `Operations.Requirements`
  and `Operations.InChannelsOrRequirements []` are vacuous for
  interaction-free, subcircuit-free lists.
* `subcircuitChannelsWithRequirements_eq_nil`, `shallowChannels_eq_nil`,
  `requirementsChannelsLawful_of_nil` — `RequirementsChannelsLawful ops [] []`
  is automatic for such lists.
* `matOps_subcircuits`, `mat_subcircuits`, `azlLoop_subcircuits`,
  `azlLinLoop_subcircuits`, `assertZeroLazy_subcircuits` and the five matching
  `*_interactions` lemmas.

Value lemmas (soundness direction):

* `flatSum`, `flatSum_append`, `flatSum_filter`, `eval_eq_constVal`,
  `flatSum_flat`, `flat_filter_isProd`, `matOut_eval`, `azlLoop_eval`,
  `azlLinLoop_eval`, `azl_eval`.

Completeness direction:

* `constraints_eval_of_complete`, `matOut_eval_complete`,
  `azlLoop_eval_complete`, `azlLinLoop_eval_complete`, `azlLoop_complete`,
  `azlLinLoop_complete`, `assertZeroLazy_complete`.

Bundled results:

* `isOnCurveSpec i := NS i[0] i[1]`
* `isOnCurveMain_soundness : FormalAssertion.Soundness Fp isOnCurveMain (fun _ => True) isOnCurveSpec`
* `isOnCurveMain_completeness : FormalAssertion.Completeness Fp isOnCurveMain (fun _ => True) isOnCurveSpec`
* `pointEqualitySpec i := i[0] = i[2]*i[3] ∧ i[1] = i[2]*i[4]`
* `pointEqualityMain_soundness`, `pointEqualityMain_completeness`
* `isOnCurveAssertion : FormalAssertion Fp (fields 2)`
* `pointEqualityAssertion : FormalAssertion Fp (fields 5)`

Soundness derives the curve equation from the enforced rows (via
`AffineBridge.short_nonsingular`); completeness uses the spec to discharge the
`assertZeroLazy` assertion row and `mat_complete` for the witness rows.

## Checks (observed)

```
lake build                                   -> Build completed successfully (17893 jobs)
lake build StandardECDSA.Main                -> green (part of the above)
lake exe standardEcdsaCheck --count-only     -> allocations=4628 rows=4634 score=9262
lake exe standardEcdsaCheck                  -> smoke test: all R1CS assertions hold with H = [1]G
lake exe standardEcdsaCheck --comparator     -> comparator: 20 cases, 0 failures
lake build Solution                          -> Build completed successfully (8997 jobs)
python3 scripts/check_axioms.py              -> Tests/Axioms.lean: 26 roots passed the permitted-axiom audit
grep -rn "sorry" StandardECDSA/              -> (no output, exit 1)
```

Count unchanged at 4628/4634 = 9262 (no circuit rows were added or removed).

## Files changed

```
?? StandardECDSA/Gadgets/AzlExplicit.lean
?? StandardECDSA/Gadgets/CurveExplicit.lean
?? StandardECDSA/Gadgets/Semantics4.lean
?? StandardECDSA/Gadgets/VarShape.lean
```

## Gadget bundling status after this round

Bundled (semantic spec + soundness + completeness + cost + R1CS):
`sel`, `muxConst4`, `affAdd`, `affDouble`, `elm`, `elmTo`, **`isOnCurve`**,
**`pointEquality`** — 8 of 9 gadget families.

Remaining for M3:

* (1) `mux4` — `ElaboratedCircuit.withData` with explicit constant
  `localLength` + `data_eq`; needs `matLen (matOut e n) = matLen e`.
* (c) comparator semantic specs (`assertLtOrderOf` / `assertLtOrderGuardedOf`),
  including the inactive overflow branch.
* (d) phase cost certificates (FixedBase 644/644, 2H/3H+tables 32/32,
  JointLadder 3070/3072) after restructuring the `[0:128]`/`[0:256]` loops.
* (e) phase semantic specs (FixedBase `ep = H + [E]G`, ShiftedTables
  `±3H + b0·Q + b1·R`, JointLadder signed-offset invariant).
