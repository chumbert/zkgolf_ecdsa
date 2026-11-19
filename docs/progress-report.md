# M2 progress report — P-256 constant certificates

Date: 2026-11-17 (session), updated 2026-11-19. Branch: `claude-ecdsa-plan`. Status: **in progress — M5 previously verified; current experiment S1 done (K modules build and sampled axiom audit); public M2 theorems still pending**.

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

## 19 November — orchestrated S1 verification

The preceding sections are preserved historical reports. The following results
were independently checked in the current experiment. The user approved the
current branch and existing-change edits, the six-step list, and starting S1.
The frozen list is `.lean-agent/steps.md`; no S2 work has started.

### Environment (`.lean-agent/env.txt`)

```text
Setup check: PASS — lean-prover replied OK
Setup session: ses_e0bd2e8fbffetyqxG12cru7WUL
Previous check: Model unavailable: mistral/mistral-medium-3.5
Configured lean-prover model: mistral/mistral-medium-2604#high
Branch override: user approved claude-ecdsa-plan and modification of existing changes
Thu 19 Nov 14:19:32 UTC 2026
1715fe608d35e4694230890e96646c1f29fe5606
claude-ecdsa-plan
df33b2c0d3c37965e51f1275d7862746a6e4514ec6553bb61567bd54d4f90118  docs/ecdsa-proof-plan.md
leanprover/lean4:v4.34.0
opencode v2.0.24
```

### Verdicts and timing

| Step | Verdict | Sorries in step files | Wall time (end − start) | Retried | Over time limit |
|---|---|---:|---:|---|---|
| S1 — K certificate modules | done | 0 | 2575 s (42m55s) | No | Yes, by 12m55s |

Totals: 1 completed step, 0 partial, 0 blocked, 0 retries, 0 S1 sorries.
Slowest and only executed step: S1. S2–S6 are not executed.
The wall time includes the subagent run, not the subsequent independent checks.

Independent checks (cached Lake builds, not clean-build benchmarks):

| Command | Wall seconds | Exit |
|---|---:|---:|
| `lake build Solution.Projected.Certs.CertsK0` | 4 | 0 |
| `lake build Solution.Projected.Certs.CertsK1` | 3 | 0 |
| `lake build Solution.Projected.Certs.CertsK2` | 3 | 0 |
| `lake build Solution.Projected.Certs.CertsK3` | 4 | 0 |
| `lake build Solution.Projected.Certs.CertsK4` | 3 | 0 |
| `lake build Solution.Projected.Certs.CertsK5` | 4 | 0 |
| `lake env lean .lean-agent/S1/Audit.lean` | 3 | 0 |

The independent build/audit commands total 24 seconds at whole-second timing
resolution. The subagent separately reported roughly 50 seconds of build time;
that is not substituted for its measured 42m55s total run.

### Proof scope and axiom evidence

Source review confirms exactly 4199 declarations `kG_ne_1` through `kG_ne_4199`,
each asserting the corresponding literal natural multiple of `G` is nonzero,
without additional hypotheses. No Lean source or generator changes were needed;
the before/after tracked diff and status matched before this report update.

The first and last declaration of each module was audited:
`kG_ne_1`, `kG_ne_700`, `kG_ne_701`, `kG_ne_1400`, `kG_ne_1401`,
`kG_ne_2100`, `kG_ne_2101`, `kG_ne_2800`, `kG_ne_2801`, `kG_ne_3500`,
`kG_ne_3501`, `kG_ne_4199` (all in namespace `Solution.Projected`).
Every print returned exactly `[propext, Classical.choice, Quot.sound]`.
The complete output is `.lean-agent/S1/checks.txt`; statement coverage is recorded
in `.lean-agent/S1/statement-review.txt`.

The S1 sorry scan and forbidden-feature scan were clean. There are **no remaining
AGENT-SORRY proof markers from S1**. This is not a repository-wide sorry-free claim:
Lake replayed an existing `honestHint` placeholder warning at
`Challenge/Instances/ECDSA_P256_Projected/Interface.lean:23`. The sampled K lemmas
do not depend on `sorryAx` according to their axiom prints.

### Assessment and deviations

- S1 meets its proof/build acceptance conditions; all checked statements are
  unchanged. No retry is needed for the mathematical result.
- The subagent exceeded its 30-minute limit and wrote orchestrator-reserved
  evidence filenames despite its prompt. Its versions were preserved as
  `agent-*.txt` / `agent-report.md`; the authoritative checks and verdict were
  produced independently. This is a workflow deviation, not an accepted agent
  self-verdict.
- The agent's returned response is saved in `subagent-response.md`. Its claim
  that the zero-case fix is working is **not established by S1**: the finite
  assembly theorem has not been built. Its stated next step (tables) is also
  incorrect for the approved list.
- The orchestrator's first timing wrapper failed because `/usr/bin/time` is
  absent; no Lean command ran in that attempt. It was rerun successfully with
  shell timestamps. The failed wrapper log is retained separately.
- No clean rebuild, exhaustive per-lemma axiom audit, public small-multiple
  theorem, table theorem, shift theorem, or aggregate M2 build was verified here.
  **M2 and the overall sorry-free, axiom-clean circuit goal remain incomplete.**

Next action: S2 — isolate and verify the full `small_multiples_ne_zero` theorem
without importing the slow table path. Retain `.lean-agent/env.txt`, `steps.md`,
and all S1 prompts, reports, logs and verdicts to reproduce this experiment.
