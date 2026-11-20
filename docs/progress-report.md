# M2 progress report — P-256 constant certificates

Updated 2026-11-20. Branch: `claude-ecdsa-plan`. **All three public M2 theorems are now independently verified in their standalone modules.** S5's full 512-entry `table_pt` builds, reproduces and passes its axiom audit. The S5 retry's strict verdict is blocked on preservation of the first attempt's audit driver, not on the mathematics. S6 has not been run by the orchestrator; the aggregate M2 acceptance check is outstanding. See the [S5 results](#20-november--s5-results); earlier entries describe their respective snapshots.

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

## 20 November — S2 results

**Proof result:** verified on retry for all naturals `0 < m < 4 * N_H`, with `N_H = 1050` and the original P-256 point `G`. **Experiment verdict:** `blocked` solely because of an unauthorized file in the ignored evidence directory. No mathematical obligation of S2 is missing. The two results are recorded separately rather than accepting the prover's own verdict or treating a bookkeeping error as a proof failure.

### Environment (`.lean-agent/env.txt`)

```text
Setup check: PASS — lean-prover replied OK without error
Setup session: ses_e082a7409ffehxV492JySnzokz
Configured lean-prover model: mistral/mistral-medium-2604#high (from ~/.config/opencode/agents/lean-prover.md)
date -u: Fri Nov 20 07:22:15 AM UTC 2026
git rev-parse HEAD: 1eda8626ff451e4c42d81a6d95e9ee9fe4c33046
Branch: claude-ecdsa-plan
sha256sum: df33b2c0d3c37965e51f1275d7862746a6e4514ec6553bb61567bd54d4f90118  docs/ecdsa-proof-plan.md
cat lean-toolchain: leanprover/lean4:v4.34.0
opencode --version: opencode v2.0.24
```

The original ignored S1 evidence and step list were absent in this checkout. S1 is carried forward from the 19 November report, not rerun. The reconstructed list was approved before S2 and then frozen (SHA-256 `7e5772c5d34a200a182793b2b5be4796982ba856cb395b0cd2c373b8385f705c`). `scripts/bootstrap.sh` succeeded in 336 s (5m36s), with no change to `git status --short`; this is setup time, not prover time.

### Verdicts and measured prover time

| Step / attempt | Verdict | Sorries in step files | Wall time (end − start) | Retried | Over time limit |
|---|---|---:|---:|---|---|
| S1 (historical) | done | 0 | 2,575 s (42m55s) | No | Yes, 12m55s |
| S2 first attempt | blocked: build failed, no axiom result | 0 | 3,185 s (53m05s) | Yes | Yes, 8m05s |
| S2 retry | blocked: file scope only; proof verified | 0 | 783 s (13m03s) | Only retry | No |

Totals through S2: two steps attempted, **1 done, 0 partial, 1 blocked** under the strict workflow; three attempts, one retry, two overruns. **6,543 s (1h49m03s)** prover wall time across attempts. **S2 was the slowest step**, 3,968 s (1h06m08s) across both attempts; its first attempt was also the slowest individual run. Independent checks and setup are excluded. S3–S6 have not run.

### What the independent checks established

- **First attempt.** A single `fin_cases` proof over `Fin 4200` listed all positive cases but did not build. `lake build Solution.Projected.Math.SmallMultiples` failed after 286 s (`Lean exited with code 137`), before the 600 s verification cap. The audit failed after 4 s because `SmallMultiples.olean` did not exist. The exit code does not establish why the process was killed. `ConstantCerts.lean` also still redeclared both names, and five temporary files were outside the permitted scratch directory. The verification wrapper's final console echo had a bad file descriptor **after** it had recorded the build, audit, and their exit codes in `checks.txt`.
- **Retry.** `Solution/Projected/Math/SmallMultiples.lean:4245` proves the original universal statement. Six private interval lemmas cover 1–700, 701–1400, 1401–2100, 2101–2800, 2801–3500 and 3501–4199. A chain of comparisons selects the interval. Source inspection found exactly the 4,199 expected `kG_ne_*` references in order, and no table certificates or aggregate in its project import path. The aggregate source now imports the extracted declarations instead of redefining them; its table and shift statements are unchanged.

| Independent retry check | Result | Wall time |
|---|---|---:|
| `lake build Solution.Projected.Math.SmallMultiples` | exit 0, cached | 2 s |
| `lake env lean Solution/Projected/Math/SmallMultiples.lean` | exit 0, checked the submitted source directly with built dependencies | 3 s |
| `lake env lean .lean-agent/S2-retry/Audit.lean` | exit 0, one expected public root | 3 s |

Actual audit output:

```text
'Solution.Projected.small_multiples_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The retry source scans found no `sorry`, `native_decide`, `axiom` or `implemented_by` in scope. No remaining `AGENT-SORRY` markers were found in project Lean sources (excluding caches and ignored experiment evidence). That does **not** make the entire circuit sorry-free: bootstrap and Lake replayed existing challenge template warnings. The two theorem results `shift_pt` and `table_pt`, a clean aggregate build and axiom audit, the <15-minute full M2 build target, and the remaining circuit obligations were **not** verified here.

**Why the strict verdict is blocked:** The retry modified only the two allowed Lean files in the versionable project, but the prover also wrote `.lean-agent/S2-retry/REPORT.txt` outside `scratch/`, contrary to the explicit allowlist. It is a duplicate prose report, not a proof input. It was preserved; it is not the authoritative `report.md` or `verdict.txt`. No third attempt was made. No proof repair is needed. The next independent proof step is **S3 (`shift_pt`)**; the user can separately accept the file-scope deviation if desired.

Evidence for this checkout: `.lean-agent/env.txt`, `steps.md`, `bootstrap/`, `S2/` and `S2-retry/` (prompts, returned reports, timings, checks, source reviews and verdicts). Keep this directory separately: Git deliberately ignores it.

## 20 November — S3 results

| Step | Verdict | Sorries in step files | Wall time (end − start) | Retried | Over time limit |
|---|---|---:|---:|---|---|
| S3 — isolated shift point | **done** | 0 | **901 s (15m01s)** | No | No (30 min limit) |

`Solution.Projected.shift_pt` ([source](../Solution/Projected/Math/ShiftCert.lean#L12)) proves the circuit's existing shift coordinates represent exactly `(4 * ((4^128 - 1) / 3)) • G`, with the unreduced natural scalar and no extra hypotheses. I compared both coordinate literals and the chain's scalar against the plan. The proof uses `cS895_curve` and `cS895_scalar`; its import path uses neither the lookup proofs nor the small-multiple assembly.

| Independent check | Result | Wall time |
|---|---|---:|
| `lake build Solution.Projected.Math.ShiftCert` | exit 0, cached | 2 s |
| `lake env lean Solution/Projected/Math/ShiftCert.lean` | exit 0, source checked directly with built dependencies | 3 s |
| `lake env lean .lean-agent/S3/Audit.lean` | exit 0, exactly the requested root | 2 s |

```text
'Solution.Projected.shift_pt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No sorries or forbidden proof constructs were found in the step scans. No remaining `AGENT-SORRY` was found in project Lean sources. Only `ShiftCert.lean` (new) and the extraction/import in `ConstantCerts.lean` changed in the project; the prover also supplied the allowed audit driver. The S2 edits to `ConstantCerts.lean` predated S3. Before/after hashes confirmed earlier work and evidence were unchanged. The subagent estimated 33 minutes, but the recorded timestamps were 08:53:59–09:09:00 UTC: **15m01s**, not an overrun. Evidence: `.lean-agent/S3/`.

**Totals through S3:** three steps attempted, **2 done, 0 partial, 1 blocked** under the strict workflow; four attempts, one retry, two overruns. Total prover time **7,444 s (2h04m04s)**, excluding setup and independent checks. S2 remains the slowest step (1h06m08s including retry). Next: **S4, build and time `CertsTab0`** before scaling to the full table. S4–S6 have not run. Neither the aggregate M2 target nor the overall sorry-free, axiom-clean circuit goal has been established.

## 20 November — S4 results and stop

**Proof result:** all 43 point entries in [CertsTab0](../Solution/Projected/Certs/CertsTab0.lean) compile, and both requested endpoint axiom audits pass. **Step verdict: blocked.** Running the maintained `scripts/gen_projected_certs.py` in isolation regenerates the old proof bodies for this module. The working technique exists in the submitted Lean source and a scratch-only script, not in the project generator. S4 used its one retry. S5 depends on S4, so neither S5 nor S6 was launched.

### Cumulative verdicts

| Step / attempt | Verdict | Sorries in scope | Wall time (end − start) | Retried | Over time limit |
|---|---|---:|---:|---|---|
| S1 (historical) | done | 0 | 2,575 s (42m55s) | No | Yes, 12m55s |
| S2 first attempt | blocked | 0 | 3,185 s (53m05s) | Yes | Yes, 8m05s |
| S2 retry | blocked: file scope only; proof verified | 0 | 783 s (13m03s) | Only retry | No |
| S3 | done | 0 | 901 s (15m01s) | No | No |
| S4 first attempt | blocked: no successful build/audit, generator mismatch | 0 | 2,252 s (37m32s) | Yes | No |
| S4 retry | blocked: pilot verified, generator mismatch | 0 | 709 s (11m49s) | Only retry | No |

**Totals:** four steps attempted, **2 done, 0 partial, 2 blocked**; six attempts, two retries, two overruns. Measured prover wall time totals **10,405 s (2h53m25s)**, excluding setup and independent checks. S4 took **49m21s** across both attempts. S2 remains the slowest step (1h06m08s) and had the slowest individual attempt (53m05s). Environment and model are unchanged from the `env.txt` block above. For the S4 retry, the recorded launch was 09:56:03 UTC and receipt was 10:07:52 UTC. On return the `start` file showed 09:56:35, 32 s later than the launch record. Both values are preserved (`start`, `start-as-returned`, `timing-review.txt`); the table uses the observed launch time. Both values are within limit.

### Independent S4 checks

- **First attempt.** Only Tab0's import changed (`Certs12` to `Certs0`); the generator still emitted `Certs12`. Two compiler processes were still running on return and were stopped before verification. An initial virtual-memory-capped check failed creating threads. A separate real pilot build with two threads timed out after 120 s (exit 124); no `.olean` was produced and the audit reported the missing object. Neither a memory diagnosis nor a speedup was established by that attempt.
- **Retry.** The original `Certs12` import was restored. Each pilot proof now supplies the certified curve witness and states the intermediate point explicitly before applying its known scalar equality; it no longer rewrites the dependent point expression. Only the proof bodies changed: comparison with pre-S4 signatures confirmed all **512 point statements and 512 coordinate equalities**, in their original modules. This comparison does not certify the other 11 modules.

| Independent retry check | Result | Wall time |
|---|---|---:|
| `lake build Solution.Projected.Certs.CertsTab0` | exit 0, cached | 2.458 s |
| `lake env lean -o .lean-agent/S4-retry/independent/CertsTab0.olean Solution/Projected/Certs/CertsTab0.lean` | exit 0, fresh pilot compilation from source; dependencies cached | 3.307 s |
| `lake env lean .lean-agent/S4-retry/Audit.lean` | exit 0, exactly the two expected declarations | 2.677 s |
| Isolated production generation, then `cmp` on each table file | **Tab0 differs**; Tab1–Tab11 byte-identical to their current sources | — |

```text
'Solution.Projected.tab_pt_0_0' depends on axioms: [propext, Classical.choice, Quot.sound]
'Solution.Projected.tab_pt_10_2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The step scans found no `sorry` or forbidden proof constructs. **Remaining `AGENT-SORRY` markers in project Lean sources: none found** (excluding build/cache and ignored evidence). This is not a repository-wide sorry-free or circuit-certification claim: existing challenge template placeholders remain, and the full table theorem, aggregate audit and circuit obligations are unverified.

The next useful assignment, if separately authorized, is **generator synchronization**: have the prover transfer the verified Tab0 proof pattern into `scripts/gen_projected_certs.py`, regenerate in an isolated directory and demonstrate byte-identical pilot output, then repeat the pilot build/audit. This would be new work, not a third attempt under this experiment. Keep `.lean-agent/S4/` and `S4-retry/` along with the environment, frozen step list, earlier evidence and this report. The authoritative regeneration comparison is in `S4-retry/generator-verify/compare.txt` and `tab0.diff` beneath that directory.

## 20 November — generator-only repair

| Assignment | Verdict | Sorries | Wall time | Retried | Over time limit |
|---|---|---:|---:|---|---|
| Supplemental generator repair (not S5) | blocked: working-tree source preservation | 0 | 806 s (13m26s) | No | No |

The maintained generator now computes the pilot's verified proof bodies. I independently ran it in an empty staging directory and compared its complete output against the manifest captured **before dispatch**: all 32 filenames and hashes match. A fresh compile of the staged pilot passed. Its first and last point lemmas reported exactly `[propext, Classical.choice, Quot.sound]` using the new `.olean` and existing dependencies. No sorries found.

The preservation check failed: the working `CertsTab0.lean` changed during the assignment from the verified `41859b0c…` to the older `427950a5…`. An additional copy also appeared in the previous retry's scratch directory. The working-tree build timed out after 20 s and its audit found no `.olean`. The other 31 working source files match the output. The independently recovered verified file is `.lean-agent/S4-generator-repair/independent/Solution/Projected/Certs/CertsTab0.lean`. I did not overwrite the working copy; restoring it needs a separate decision because the authorization was generator-only. S4's historical verdict is unchanged. The supplemental assignment brings total prover time to 11,211 s (3h06m51s), without changing the frozen S1–S6 list. S5 remains paused.

## 20 November — pilot restoration

| Assignment | Verdict | Sorries | Wall time (end − start) | Retried | Over time limit |
|---|---|---:|---:|---|---|
| Restore only `CertsTab0.lean` | **done** | 0 | **54 s** | No | No (15 min limit) |

Before/after project hashes show that the prover changed only `Solution/Projected/Certs/CertsTab0.lean`; earlier evidence was unchanged. The file matches the independently verified copy byte for byte (SHA-256 `41859b0c937bca9263ba70c46d9015d94222805ab46a7049fa88690982d1d113`). I reran the maintained generator in an empty staging directory: **all 32 output files** matched both the current working tree and the pre-repair manifest. This compares bytes; it does not compile the other 11 table modules.

The independent `lake build Solution.Projected.Certs.CertsTab0` passed in 2.438 s (cached); a separate fresh compile of the restored source passed in 3.327 s with existing dependencies. The endpoint audit passed in 2.683 s: `Solution.Projected.tab_pt_0_0` and `Solution.Projected.tab_pt_10_2` both use exactly `[propext, Classical.choice, Quot.sound]`. The step scans found no `sorry` or forbidden proof construct, and no `AGENT-SORRY` markers were found in project Lean sources. Evidence: `.lean-agent/S4-pilot-restore/`.

The pilot build and reproducibility conditions now hold in the working tree. This resolves the practical S4 blocker without changing its historical verdict. Cumulative prover time including both supplemental assignments is **11,265 s (3h07m45s)**; S2 remains the slowest step. S5 and S6 have not run, and the overall circuit goal is not yet verified.

## 20 November — S5 results

**Proof:** [`Solution.Projected.table_pt`](../Solution/Projected/Math/TableCert.lean#L23) is verified for each `i : Fin 128` and `d : Fin 4`. The point uses the actual `tableX i d` and `tableY i d`, and the scalar is the unreduced natural number `(4 + d.val) * 4^i.val`. There are no additional hypotheses. The theorem does not depend on the small-multiple assembly or `CertsFinal`.

S5 resumed at HEAD `81552c4df860c233aa437f5480c1ee84d79a73fb` after the user committed previous results. Model, toolchain, plan and frozen step list remained as recorded above. The existing untracked `opencode.json` was preserved.

| Step / attempt | Verdict | Sorries in scope | Wall time (end − start) | Retried | Over time limit |
|---|---|---:|---:|---|---|
| S5 first attempt | blocked: `CertsTab1` stalled, no build or axiom result for `table_pt` | 0 | 6,450 s (1h47m30s) | Yes | Yes, 1h02m30s |
| S5 retry | blocked: prior evidence not preserved; **proof verified** | 0 | 430 s (7m10s) | Only retry | No |

The first attempt drafted the public declaration but left the generator's fast proof restricted to Tab0. It was still compiling Tab1 more than an hour past its deadline when interrupted. Independent bounded builds timed out on `CertsTab1` and `TableCert`, and the audit reported the missing `.olean`. The time limit should have been enforced earlier. A separate 45-minute external cutoff was armed for the retry and disarmed on its return.

The retry generalized the pilot proof in the maintained generator to all entries. I compared the **512 point statements and 512 coordinate equalities** against their pre-S5 signatures and module assignments; all were unchanged. The public proof dispatches to each expected entry exactly once. The pilot's bytes remain unchanged. Generating all 32 certificate files in a fresh staging directory reproduced the complete working generated directory byte for byte.

| Independent retry check | Result | Wall time |
|---|---|---:|
| Individual `lake build` for `CertsTab0`–`CertsTab11`, in order | all 12 passed, cached | 2.338–2.538 s each |
| Fresh source compilation, one new `.olean` per table module | all 12 passed with dependencies cached | 39.958 s total |
| `lake build Solution.Projected.Math.TableCert` | passed, cached | 2.428 s |
| Fresh source compilation of `TableCert` | passed | 4.828 s |
| `lake env lean .lean-agent/S5-retry/Audit.lean`, importing only `TableCert` | passed; named root checked | 2.463 s |

```text
'Solution.Projected.table_pt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No step `sorry` or forbidden proof constructs were found. No remaining `AGENT-SORRY` markers were found in project Lean sources (excluding cache and experiment evidence). All versionable changes were within the step's allowlist. **Strict workflow failure:** `.lean-agent/S5/Audit.lean` was present before the retry and absent afterwards, contrary to the no-changes-to-prior-evidence rule. The retry's allowed `.lean-agent/S5-retry/Audit.lean` has precisely the missing file's SHA-256, `9b9ecfd15c19b6f70bbe12c0d325444c2cdb0a94d9558784272c253873c4676e`. No proof repair is needed; no third attempt was made. The prover also reported building `ConstantCerts`, contrary to the S5 brief; its aggregate claims are not accepted as an independent S6 build or audit.

**Cumulative totals:** five numbered steps attempted, **2 done, 0 partial, 3 blocked** by their historical strict verdicts, including verified mathematical results with workflow failures. Eight numbered attempts, three retries, three overruns. Numbered steps account for 17,285 s (4h48m05s); with the two supplemental assignments, total prover time is **18,145 s (5h02m25s)**. **S5 was the slowest step** at 6,880 s (1h54m40s) across its two attempts. Times exclude setup and independent verification. Evidence is under `.lean-agent/S5/` and `S5-retry/` (including `checks.txt`, all per-target timings, the source/manifest review and verdicts). S6 has not started. A clean full-M2 time and the overall sorry-free, axiom-clean circuit goal remain unverified.
