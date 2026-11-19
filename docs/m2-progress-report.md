# M2 progress report — P-256 constant certificates

Date: 2026-11-17 (session), updated 2026-11-19. Branch: `claude-ecdsa-plan`. Status: **in progress — M5 verified; M2 split into subtasks, Fin 4 case-split verdict done, generator patch in flight**.

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

**First task: test the case split, not its scale.** DONE 2026-11-18 (subagent
`m2-fin4-test`). The generator splits on `Fin 4200` but emits branches for
positive multiples starting at 1. Reproduced the proof shape on `Fin 4` in
scratch files (`/tmp/m2_fin4_naive.lean`, `/tmp/m2_fin4_fixed.lean`), run with
`lake env lean`. **Verdict: `fin_cases` DOES leave a zero goal** — the naive
shape fails (`unsolved goals case «3»`, positive facts land on the wrong cases);
the fixed shape passes:

```lean
fin_cases i
· exact absurd hpos (by simp)   -- zero case, closed from positivity
· exact h1 (by decide)
· exact h2 (by decide)
· exact h3 (by decide)
```

(after `fin_cases`, per-case equalities are `↑⟨k, ⋯⟩ = n`, so `rfl` does not
typecheck — `by decide` proves them). Both runs ~23 s wall (Mathlib import
overhead). Next: patch the generator to emit the fixed shape, then scale up.

**Handoff by theorem.** Give each public theorem its own buildable module and
axiom check, keeping `ConstantCerts` as the aggregate import. These are proposed
targets, not completed proofs:

| Theorem | Unblocks | Verification status |
|---|---|---|
| `table_pt` | C1 fixed-base table entries | Build and axiom check pending |
| `shift_pt` | C1 initial shift | Build and axiom check pending |
| `small_multiples_ne_zero` | M3 offset injectivity | `Fin 4` case-split verdict done (zero goal confirmed, fixed shape verified); generator patch + `Fin 4200` build pending |

Record each module's build command, elapsed time and `#print axioms` output.
C1 can use the two verified fixed-base results without waiting for M3's result.
Close M2 only after all three pass the allowed-axiom audit and
`lake build Solution.Projected.Math.ConstantCerts` succeeds.

## 18–19 November session (subagent split, M5 done)

M2 was split into small subagent subtasks with per-step reporting (per §13
briefing template). Subagent model: `mistral-large-4` (session `active_model =
"large"`); the installed `lean` profile (`leanstral`) was not used.

- **`m2-fin4-test`** (completed): Fin 4 verdict above.
- **`m2-gen-fix` / `m5-bits`** (failed at turn 1): infrastructure error
  `[Errno 8] nodename nor servname provided, or not known` — DNS resolution
  failure when the child called the model API; not a task failure. Network
  verified reachable afterwards (`curl https://api.mistral.ai/v1/models` → 401).
  Both were respawned as `m2-gen-fix-r2` / `m5-bits-r2`.
- **`m5-bits-r2`** (completed, M5 verified): `Solution/Projected/Math/Bits.lean`
  with all five lemmas proved — `field_sum_eq_natCast`, `nat_sum_lt`,
  `val_field_sum`, `exists_bool_decomp`, `digest_lift`. `lake build
  Solution.Projected.Math.Bits` green in 1m23s; `#print axioms` on all five =
  `[propext, Classical.choice, Quot.sound]`. No sorry/native_decide/axiom; no
  frozen-interface changes. M5 ready for G8 and C3.
- **`m2-gen-fix-r2`** (completed 2026-11-19): generator patched — the emitted
  `small_multiples_ne_zero_aux` now reads `intro fm hpos; fin_cases fm` with the
  zero case closed by `exact absurd hpos (by simp)` and positive cases by
  `kG_ne_m`. Regenerated (`13 chunk + 12 tab + 6 kG + 1 final, 5094 blocks`,
  0.38 s). Single-module validation: `lake build Solution.Projected.Certs.CertsK0`
  PASS in 9.4 s (deps cached). Warning: `CertsTab0` alone ran >40 min on the
  `rfl`-heavy tab lemmas — the `CertsTab*` chain is the known bottleneck.
  No sorry/native_decide/axiom in generated paths (grep clean).
- **`m2-certs`** (original monolithic agent): interrupted and idle; its
  uncommitted changes to `scripts/gen_projected_certs.py` and
  `Solution/Projected/Certs/CertsFinal.lean` remain in the working tree and are
  the base for `m2-gen-fix-r2`.

**Next subtasks (queued):** build the `CertsK*` chain → axiom-check
`small_multiples_ne_zero` (zero case now fixed); build the `CertsTab*` chain
(>40 min for Tab0 alone — run per-file with recorded times) → axiom-check
`table_pt` / `shift_pt`; final
`lake build Solution.Projected.Math.ConstantCerts` + full axiom audit to close
M2.

**Snapshot 2026-11-19 11:57 CET:** `m2-kg-chain` running (CertsK* per-module
builds + `small_multiples_ne_zero` axiom check); no new Certs oleans in the last
30 min yet. All other M2 subtasks idle/completed; M5 closed.

**Update 2026-11-19 (later):** `m2-kg-chain` was interrupted at user request
before reporting — no per-module build table or axiom output was produced, so
`small_multiples_ne_zero` remains **pending**. M2 pipeline paused; resume by
respawning the `CertsK*` chain task, then `CertsTab*`, then the final
`ConstantCerts` assembly + axiom audit.
