# M3 report — round 15 (items (e3-final) and (e4))

## Timing

| | value |
|---|---|
| before (`date -u +%s`) | **1795036184** |
| after (`date -u +%s`) | **1795042972** |
| elapsed_seconds | **6788** |

## Milestone status: **M3 COMPLETE**

All M3 items are now closed:

| item | content | state |
|---|---|---|
| (1) | per-gadget/phase cost certificates | closed (earlier rounds) |
| (2) | `IsR1CSCirc` per-expression-shape lemmas | closed (earlier rounds) |
| (3a) | field-level `FormalAssertion` bundling | closed (earlier rounds) |
| (3)(4) | 9 gadget families bundled (sel, muxConst4, affAdd, affDouble, elm, elmTo, isOnCurve, pointEquality, mux4) | closed (earlier rounds) |
| (3c) | comparator semantic specs (`assertLtOrderOf`, `assertLtOrderGuardedOf`) | closed (earlier rounds) |
| (d) | phase cost certificates 644/644, 32/32, 3070/3072 | closed (earlier rounds) |
| (e1) | `shiftedTables` group spec | closed (round 10) |
| (e2) | T11 fixed-table kernel certification | closed (round 11) |
| (e3) | `fixedBase_spec` | **closed this round** |
| (e4) | `jointLadder_spec` | **closed this round** |

## What was proved this round

### `StandardECDSA/Phases/FixedBaseSemantics.lean` (item (e3-final))

* `fin_foldl_inv'` — generic invariant induction for `Fin.foldl` with the step
  hypothesis stated at the *actual* accumulator (needed because the row
  constraints are only available at the real accumulator).
* `soundness_append_foldlRange` — split a phase into a prefix and a
  `foldlRange` loop, exposing the loop's per-step row constraints.
* **`fixedBase_spec`** — from any satisfying assignment of
  `(fixedBase h eb).operations n`, with Booleanity of the 256 digest bits and
  the 129 distinct-`x` conditions,
  `∃ hns, some (eval out.1) (eval out.2) hns = H + toAffineLift (digestNat env eb • Gpt)`.

### `StandardECDSA/Phases/JointLadder.lean`

* `jointLadderBody`, `jointLadderFinal`, `jointLadder` rewritten as explicit
  lambdas (not `do` blocks) so `.operations n` reduces to a `++` in one step.
* `jointLadderBody_eq_bind` — `jointLadderBody … = mux4W … >>= fun t => elm acc t`
  (the shape `CostIs.bind` produces).
* `jointLadderFold_localLength` (= 3060), `jointLadderBody_ops`,
  `jointLadderBody_out`, `jointLadderFinal_ops`, `jointLadder_ops`,
  `jointLadder_out`.

### `StandardECDSA/Phases/LadderSemantics.lean` (new, 616 lines) — item (e4)

Row-level, offset-generic gadget soundness:

* `elm_sound` — from the six `elm` rows at offset `n`, the output wires
  `n+4, n+5` are `2 • P + Q`.
* `elmTo_sound` — from the six `elmTo` rows, `2 • P + Q = target`.
* `mux4W_sound` — the six `mux4W` rows select the `b0 + 2*b1` table entry.

Signed-offset ladder algebra:

* `sigma` (`= (-1)^j`), `rBitAt`, `tBitAt` (MSB-first: index `255 - j`),
  `Tpt`, `ladAcc`, `ladAccH`, `ladAccQ`, `ladAccR`, `ladInv`.
* `ladAcc_split`, `ladAccH_eq`, `bitSum`, `bitSum_succ`, `ladAccQ_eq`,
  `bitSumT`, `bitSumT_succ`, `ladAccR_eq`.
* `rBitAt_eq`, `tBitAt_eq`, `bitSum_256`, `bitSumT_256`.
* **`ladAcc_256`** — sign cancellation:
  `ladAcc … 256 = (leNat rBits : ℤ) • Qpt + (leNat tBits : ℤ) • Rpt - Hpt`.
* `sel_eq_of_bits`, `ite_beq_one`, `mux4W_Tpt` (the mux output's group point is
  `Tpt … j`, given the shifted-table contract).
* `foldlAcc_eq_ladder` — `foldlAcc` for the ladder body with local length 12.
* `soundness_foldlRange_of_eq` — per-step row constraints of a `foldlRange`
  loop from an abstracted operation list.
* **`jointLadder_spec`** — the phase spec. From *any* satisfying assignment of
  `(jointLadder acc0 tables rb sb target).operations n`, given
  * `acc0 = -H` (as a group point),
  * Booleanity of both 256-bit vectors `rb`, `sb`,
  * the shifted-table contract `Tpt`-shape for all `j < 256`,
  * `NS` of the target coordinates,

  the target is `[r]Q + [t]R - H`:
  `∃ hns, some (eval target.1) (eval target.2) hns
     = (leNat rBits : ℤ) • Qpt + (leNat tBits : ℤ) • Rpt - Hpt`.

  The 255 returning steps are handled by `fin_foldl_inv'` with the
  signed-offset prefix invariant `ladInv`; the final step is the `elmTo`
  assertion to the target; sign cancellation is `ladAcc_256`.

### `StandardECDSA/Phases/Cost.lean`

* `jointLadderBody_cost` now rewrites with `jointLadderBody_eq_bind` instead of
  asking the elaborator for the `>>=` defeq.
* `jointLadder_cost` re-proved at the `operationCount` level
  (`jointLadder_ops` + `Lemmas.operationCount_append` + `CostIs.foldlRange` +
  `jointLadderFinal_cost` + `decide`), because `CostIs.bind` would need the
  defeq `jointLadder = foldlRange … >>= …` and `Circuit.bind` destructures its
  first argument, unfolding the whole 255-step fold.

### `StandardECDSA/Main.lean`

* added `import StandardECDSA.Phases.LadderSemantics` so the new phase spec is
  in the `StandardECDSA.Main` build graph.

## Root cause of the recursion-depth failures (recorded for M4/M5)

`Circuit.operations` is `@[reducible]` and `List.append` matches on its **first**
argument.  Therefore *any* `isDefEq` check that mentions
`(foldlRange 255 …).operations n ++ …` whnf-unfolds the entire 255-step
`Fin.foldl` and exceeds the default recursion budget (128 steps is fine, 255 is
not).  Consequences and the fixes used:

* `soundness_append` / `soundness_foldlRange` cannot be *applied* to a
  hypothesis whose type contains the concrete fold.  Split with `rw`
  (`Operations.forAllNoOffset_append`, `Circuit.foldlRange.forAllNoOffset`)
  instead — `rw` matches syntactically and never whnf's the fold.
* `CostIs.bind` cannot be applied when the loop is the first component of the
  `>>=`; prove the `CostIs` goal at the `operationCount` level instead.
* `elmTo_sound` cannot be applied to the invariant at `Fin.foldl …`; rewrite the
  invariant to the `foldlRange … .output n` form first (`rw [← hfold] at hP`).

## Checks (observed)

```
$ lake build StandardECDSA.Main
Build completed successfully (9015 jobs)

$ lake build StandardECDSA.Phases.Cost
Build completed successfully

$ lake exe standardEcdsaCheck --count-only
Standard P-256 ECDSA circuit (6 fixed inputs)
allocations=4628 rows=4634 score=9262

$ grep -rn "sorry" StandardECDSA/
(no output, exit 1)

$ python3 scripts/check_axioms.py
Tests/Axioms.lean: 26 roots passed the permitted-axiom audit

$ #print axioms jointLadder_spec
'StandardECDSA.Phases.jointLadder_spec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
$ #print axioms fixedBase_spec
'StandardECDSA.Phases.fixedBase_spec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

Note: `lake build` with no arguments only builds the `@[default_target]`
`Challenge` and `vectors` targets (17,893 jobs) and does **not** build
`StandardECDSA`; `lake build StandardECDSA.Main` is the meaningful check.

## Remaining sorries

```
$ grep -rn "sorry" StandardECDSA/
$ echo $?
1
```

Zero hits.

## Build errors

None.

## Files changed

```
 M StandardECDSA/Main.lean                      |   1 +
 M StandardECDSA/Phases/Cost.lean               |  22 +--
 M StandardECDSA/Phases/FixedBaseSemantics.lean | 204 +++++++++++++++++
 M StandardECDSA/Phases/JointLadder.lean        | 130 +++++++---
?? StandardECDSA/Phases/LadderSemantics.lean    | 616 (new)
```

## Next milestone

**M4** — T03 `Math/SignatureEquation.lean` (`standard_iff_signaturePoint`,
`x_mod_order_iff_lift`), T14 `Math/OffsetCandidates.lean` (`Fin 1040`
candidates, `exists_goodOffset` via `exists_avoiding_injective_equations` over
the 1039-slot family in `Math/OffsetConditions.lean`), T16
`Witness/Generate.lean` + `Witness/Correctness.lean` (`generateSeed_complete`,
bounded `H` search, malformed-input handling).
