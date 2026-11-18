# M2 progress report — P-256 constant certificates

Date: 2026-11-17 (session). Branch: `claude-ecdsa-plan`. Status: **in progress, M2a partially verified**.

## Work reported on 17 November

All changes are uncommitted working-tree changes on top of `9765734` (M4/M1).

1. **`scripts/gen_projected_certs.py`** (generator, fixed and extended):
   - Added missing `import Solution.Projected.Constants` to generated headers
     (fixed "unknown identifier `tableX`/`tableY`" cascade in every tail file).
   - Tail (tab lemmas, `table_pt_aux`, `shift_pt_aux`, `kG_ne` lemmas,
     `small_multiples_ne_zero_aux`) is emitted as chained `CertsT*.lean` files
     instead of being appended to the last chunk, so heavy `fin_cases` proofs
     are separated (the chained imports still serialize the tail).
   - `table_pt_aux` now uses per-case `tab_pt_{i}_{d}` lemmas closed with `exact`
     (defeq) instead of `rw` after `fin_cases` (which produces `⟨i, ⋯⟩` literals
     that don't syntactically match `OfNat` literals).
   - Generated headers set `maxRecDepth 1000000` and `maxHeartbeats 8000000`.
   - Output: 13 chunk files (`Certs0..12`, ~5094 affine-step blocks) + 15 tail files.
2. **`Solution/Projected/Certs/Certs*.lean`** — regenerated (untracked).
3. **`Solution/Projected/Math/ConstantCerts.lean`** — imports the last tail file
   (`CertsT14`); assembles `table_pt`, `shift_pt`, `small_multiples_ne_zero`
   from the generated `_aux` theorems.
4. **`Solution/Projected/Math/CertSteps.lean`** — step lemmas (`add_step`,
   `double_step`, `curve_of_nat`, `pt_ne_zero`) bridging Nat-level `decide`
   certificates to group equations via `AffineBridge`.
5. **`docs/ecdsa-proof-plan.md`** — M2 section updated with implementation notes
   and the CertsT0/fin_cases plan.

## Verified in the 17 November session

- `lake build Solution.Projected` succeeds for all 13 chunk files
  (`Certs0..12` oleans produced) — the ~5000 affine-step certificates compile.

## Not yet verified

- Full build of `Solution.Projected.Math.ConstantCerts` (tail files pending).
- Axiom audit (`#print axioms` on the three theorems) not yet run clean.

## Difficulties encountered

1. **Missing import cascade:** generated files referenced `tableX`/`tableY`/
   `shiftX`/`shiftY` without importing `Solution.Projected.Constants`; errors
   surfaced as "Function expected" (autoImplicit) and 100-error cutoffs.
2. **`rw` after `fin_cases` fails:** `fin_cases` on `Fin 128`/`Fin 4` produces
   `⟨24, ⋯⟩` anonymous-constructor literals; `rw [tab_24_0.1]` can't match the
   `OfNat`-literal statement. Fixed with `exact tab_pt_{i}_{d}`.
3. **`maxRecDepth` exceeded:** `decide` on `tableX i d = ...` kernel-reduces
   `tableXList.getD` over a 128×4 nested literal list. Fixed with
   `set_option maxRecDepth 1000000`.
4. **Heartbeat timeout at `whnf`/`isDefEq` (200k):** elaborating `decide` on the
   tab lemmas. Mitigated with `maxHeartbeats 8000000`; planned further fix is
   `constructor <;> rfl` instead of `decide` (see plan §CertsT0).
5. **Build time:** chunk files alone took ~8 min; the tail (512 tab lemmas +
   `fin_cases` over `Fin 4200`) is the bottleneck — one full attempt ran ~12 min
   and failed only in `CertsT0`. Plan: smaller tail chunks + per-file builds.

## Next assignment

**18 November source update (not a build result).** The [generator](../scripts/gen_projected_certs.py)
already emits `constructor <;> rfl` for table equalities and splits the tail into
independently buildable `CertsTab*` and `CertsK*` modules. `CertsFinal` assembles
both, and [ConstantCerts](../Solution/Projected/Math/ConstantCerts.lean) imports it.
Do not repeat the `CertsT0` changes or start with a full rebuild.

**First task: test the case split, not its scale.** The generator splits on
`Fin 4200` but emits branches for positive multiples starting at 1. This suggests
a zero-case mismatch; it is not a confirmed build failure. In a scratch Lean
file, reproduce the same proof shape on `Fin 4` with the positivity hypothesis
and facts for 1, 2 and 3. Run `lake env lean <scratch-file>`. Check whether
`fin_cases` leaves a zero goal; if it does, close it from positivity before
applying the three facts. Record the command and outcome before scaling up.
If blocked, use the [briefing stop rule](./ecdsa-proof-plan.md#13-briefing-template-for-subagents)
and switch to independent work such as M5 rather than retrying the full build.

**Handoff by theorem.** Give each public theorem its own buildable module and
axiom check, keeping `ConstantCerts` as the aggregate import. These are proposed
targets, not completed proofs:

| Theorem | Unblocks | Verification status |
|---|---|---|
| `table_pt` | C1 fixed-base table entries | Build and axiom check pending |
| `shift_pt` | C1 initial shift | Build and axiom check pending |
| `small_multiples_ne_zero` | M3 offset injectivity | Build and axiom check pending; start with `Fin 4` |

Record each module's build command, elapsed time and `#print axioms` output.
C1 can use the two verified fixed-base results without waiting for M3's result.
Close M2 only after all three pass the allowed-axiom audit and
`lake build Solution.Projected.Math.ConstantCerts` succeeds.
