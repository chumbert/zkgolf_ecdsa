# Lean-agent experiment report — `docs/ecdsa-proof-plan.md` (Track A)

**Status: stopped at S5.** S5 is blocked after its retry, and every later step depends on it.

## Environment (`env.txt`)

```
== date -u
Thu Nov 19 12:59:53 UTC 2026
== git rev-parse HEAD
40fd170012df760b743d79d1373d69c57ff9d7b0
== branch
(detached HEAD; plan names branch circuit_baseline)
== plan sha256
165cbd4a8161f6d30774f3daebe1a0bd7d40a569c59fe675c2f2df71c1bf496c  docs/ecdsa-proof-plan.md
== vibe --version
vibe 3.1.3
== lean-toolchain
leanprover/lean4:v4.34.0
== active_model
11:active_model = "mistral-medium-3.5"   # catalog alias → mistral-vibe-cli-latest, 262k context
== setup check (rc=0), assistant reply:
['OK']
```

## Runs

| step | verdict | sorries | wall | lake/lean | other tools | model | tokens | vibe outcome |
|---|---|---|---:|---:|---:|---:|---:|---|
| S1 T0.1a | done | 0 | 2m21s | 56s | 1s | 1m24s | 722,333 | finished |
| S2 T0.1b | blocked | 0 (10 template) | 4m43s | 1m41s | 3s | 2m58s | 3,343,384 | finished |
| S2-retry | done | 0 (10 template) | 2m41s | 48s | 1s | 1m52s | 1,622,378 | finished |
| S3 T0.2a | blocked | 0 | 4m35s | 28s | 40s | 3m27s | 1,698,819 | finished |
| S3-retry | done | 0 | 58s | 8s | 0s | 50s | 584,096 | finished |
| S4 T0.3 | blocked | 0 | 7m06s | 2m02s | 13s | 4m51s | 5,912,130 | finished |
| S4-retry | done | 0 | 5m12s | 1m48s | 2s | 3m21s | 4,686,606 | finished |
| S5 T0.2b | blocked | 14 scaffold + 6 unmarked (in defs) | 11m30s | 2m05s | 2s | 9m23s | 11,393,192 | finished |
| S5-retry | blocked | 14 scaffold (file does not build) | 22m29s | 5m28s | 0s | 17m01s | 13,707,859 | turn_limit |
| **Total** | 4 done, 1 blocked (S5) | – | **61m35s** | **15m24s** | **1m02s** | **45m07s** | **43,670,797** | |

* The slowest run was S5-retry (22m29s); it hit vibe's 150-turn limit.
* `tokens` is `usage.total_tokens` from `export.json`. It appears to be summed over all turns, so it includes re-sent context, not unique tokens.
* Tool times come from the `effect` entries in `stream.jsonl`. "lake/lean" means the command contains `lake` or `lean`.

## Step results

* **S1**: done. The trusted `Spec` matches D1 word for word. `spec_iff_boundLF` is proved by `rfl`, with standard axioms only.
* **S2**: blocked on the first run. `honestHint` was declared inside the `Interface` namespace and was missing from `definition_names`, so no solution could supply it; the agent had also edited S1's files. The retry is a faithful copy of the digest template, plus `honestHint` (template sorry, listed in `definition_names`) and `ProverAssumptions := ProverAssumptionsWith honestHint`. S1's files were restored byte for byte.
* **S3**: blocked on the first run because the gadget input structs were missing. The retry added all 7.
* **S4**: blocked on the first run because the test was a sampled `#eval` that could not fail the build. The retry uses `#guard` over all 512 entries plus the shift, and indexes with `getD`. My own probe confirmed the tables are 128×4 and that a wrong `#guard` fails.
* **S5**:
  * The first attempt was not Clean formal circuits. Its theorems were vacuous (several were tautologies). `mux4` used constant points and miscomputed a coefficient. `muxConst4` was unsound (an unconstrained `b0*b1` allocation) and added rows. It also had `def … := sorry` placeholders.
  * The retry has the right shape (`FormalCircuit`/`FormalAssertion` with Clean `Soundness`/`Completeness` statements, 14 marked SCAFFOLD-SORRY), but `lake build Solution.Projected.Gadgets` fails at `bit3` and `isOnCurve`, and the run ended on the turn limit.

## Remaining sorries

* `Solution/Projected/Gadgets.lean`: 14 `-- SCAFFOLD-SORRY: proved in G1/G2/G3/G6` sorries, in a file that does not compile.
* `Challenge/Instances/ECDSA_P256_Projected/{Challenge,Interface}.lean`: 10 `TEMPLATE-SORRY` placeholders. These are intentional and mirror the digest template.
* No `AGENT-SORRY` was used.

The plan's goal, sorry-free and axiom-clean theorems, is **not met**. Only T0.1, T0.3 and the first part of T0.2 are done. None of the plan's proof tasks (M*, G*, C*, O*, F1) has started.

## Assessment

* **Matches the plan:** the trusted contract (T0.1 with D1 and D2), the `SolutionProjected` library and types, and the literal constant tables with full executable cross-checks (T0.3).
* **Doesn't match:** T0.2's gadget layer. The agent repeatedly produced plausible but wrong code: vacuous specs, cost changes, and an unsound mux. It needed the specific defect list from review to get close, and still did not compile within 150 turns.
* **Pattern:** 4 of 5 first attempts were rejected. Three passed every mechanical check (build, sorry grep, banned-construct grep) and failed only on review against the plan text.
* **Could not verify:** whether the comparator accepts the S2 template shape (no `leanprover/comparator` checkout). The S5 per-gadget costs were never measured, because the file doesn't build.
* **Process incidents:**
  * `.lean-agent/` already held an earlier experiment (18 Nov, "Plan B", plan sha `655a14ff…`). My setup overwrote its `steps.md`, `env.txt`, `.gitignore` and S1 prompt/stream before I noticed. Everything else is moved to `.lean-agent/prev-20261118/`. Its `env.txt` survives inside its `report.md`; its `steps.md` is lost.
  * The first S1 monitor fired DONE on that experiment's stale `end` file. I re-armed it, and the S1 result above is from the real run.
* **Working tree:** all changes are uncommitted on detached HEAD `40fd170`.

## Options to continue

1. Resume S5 a third time. This breaks the one-retry rule, so it needs your OK.
2. Raise `--max-turns` or the time limit for S5 only.
3. Stop the experiment here.

## Update: S5 finished by Claude (outside the protocol)
At the user's request, Claude wrote S5 directly; it is not part of the Mistral table above. Result: **done**. `Gadgets.lean` builds,
8 gadgets, all 16 soundness/completeness theorems proved (0 sorry, standard axioms), and per-gadget costs equal the baseline.
Details and a post-mortem of Mistral's two S5 runs are in `.lean-agent/report-S5-claude.md`. S6 and later steps are not started.
