# M6 — Release: structural/cost proofs, audit, regressions, contract verifier

Milestone **M6** of `docs/ecdsa-proof-plan.md` (tasks T18, T19, T20), plus the
status of the three honest gaps (G1, G2, G3) carried over from M5.

Timing protocol: `before = 1795057746`, `after = 1795059473`,
`elapsed_seconds = 1727`.

## 1. Exact score

| quantity | value |
|---|---|
| allocations | **4 628** |
| rows (constraints) | **4 634** |
| score | **9 262** |

This matches the plan's proposed budget of 4 628 + 4 634 = 9 262 **exactly** —
there is no delta to explain. The number is *certified*, not merely measured:
`StandardECDSA.main_cost : CostIs (main inputVar) ⟨4628, 4634⟩` is a theorem
(`StandardECDSA/Cost.lean`), and the executable
`lake exe standardEcdsaCheck --count-only` independently prints
`allocations=4628 rows=4634 score=9262`.

Per-phase ledger (all certified by `CostIs` theorems):

| phase | allocations | rows |
|---|---|---|
| `seedPhase` | 4 | 1 |
| `curvePhase` | 6 | 9 |
| `nonzeroPhase` | 2 | 2 |
| `bitsPhase` | 768 | 768 |
| `bindPhase` | 0 | 4 |
| `cmpPhase` | 102 | 102 |
| `fixedBase` | 644 | 644 |
| `shiftedTables` | 32 | 32 |
| `jointLadder` | 3 070 | 3 072 |
| **total** | **4 628** | **4 634** |

## 2. Proof and audit roots

Exported theorems (all in `StandardECDSA/Main.lean`, all referring to the
actual circuit `main`):

| theorem | statement (abbreviated) |
|---|---|
| `main_soundness` | `ConstraintsHold.Soundness env ((main inp).operations n) → standardVerify …` — unconditional over every satisfying assignment of all auxiliary wires |
| `main_complete_with_seed` | `env.UsesLocalWitnessesCompleteness n … → CompleteWitness inp env n → ConstraintsHold.Completeness env ((main inp).operations n)` |
| `main_completeness` | `(∃ env, UsesLocalWitnessesCompleteness ∧ CompleteWitness) → ∃ env, ConstraintsHold.Completeness env …` |
| `main_accepts_iff_standard` | `ConstraintsHold.Soundness penv ((main inp).operations n) ↔ standardVerify …` |
| `main_cost` | `CostIs (main inputVar) ⟨4628, 4634⟩` (`StandardECDSA/Cost.lean`) |

Supporting roots audited alongside them:

* `StandardECDSA.Math.{standard_iff_signaturePoint, x_mod_order_iff_lift,
  signature_equation_iff, offsetCandidate_injective, exists_goodOffset,
  findGoodOffset_spec}`;
* `StandardECDSA.Math.{n_prime, addOrderOf_Gpt, card_eq_n, nsmul_eq_zero,
  nsmul_injective_of_lt}` (P-256 group-order certificate);
* `StandardECDSA.Math.FixedTables.{mulG_toMathlib, mulG_affine_some,
  fixedTables_get, fixedShift_eq}` (T11 fixed-table certificate);
* `StandardECDSA.Witness.generateSeed_complete`;
* `StandardECDSA.Phases.{fixedBase_spec, shiftedTables_spec, jointLadder_spec,
  fixedBase_cost, shiftedTables_cost, jointLadder_cost}`;
* `StandardECDSA.{curvePhase_cost, bitsPhase_cost, cmpPhase_cost}`.

**Axiom audit:** `python3 scripts/check_standard_ecdsa_axioms.py` audits all 30
roots above and reports

```
Tests/StandardECDSA/Axioms.lean: 30 roots passed the permitted-axiom audit
(permitted: ['Classical.choice', 'Quot.sound', 'propext'])
```

The script is fail-closed: it carries an explicit `REQUIRED` list, rejects a
missing or extra root, rejects a non-zero Lean exit, and rejects any axiom
outside `propext`, `Classical.choice`, `Quot.sound`.

## 3. Validation commands and observed results

All commands were run in this worktree; every result below is observed, not
inherited.

| command | observed result |
|---|---|
| `lake build` (whole project) | green |
| `lake build StandardECDSA.Main` | green |
| `lake build StandardECDSA.Cost` | `Build completed successfully (9021 jobs)` |
| `lake build Tests.StandardECDSA.Axioms` | `Build completed successfully (9022 jobs)` |
| `grep -rn "sorry" StandardECDSA/` | exit 1, **zero** hits |
| `lake exe standardEcdsaCheck --count-only` | `allocations=4628 rows=4634 score=9262` |
| `lake exe standardEcdsaCheck` | `smoke test: all R1CS assertions hold with H = [1]G` |
| `lake exe standardEcdsaCheck --export=/tmp/ecdsa_export` | `export: 4634 rows, 4634 wires, 0 undecomposable` |
| `lake exe standardEcdsaTests` | `regressions: 46 passed, 0 failed` |
| `python3 scripts/check_standard_ecdsa_axioms.py` | `30 roots passed the permitted-axiom audit`, exit 0 |
| `python3 scripts/check_standard_ecdsa_contract.py` | `contract: all checks passed`, exit 0 |
| `python3 scripts/check_standard_ecdsa_matrices.py /tmp/ecdsa_export` | `matrices: all checks passed`, exit 0 |

### 3.1 Contract verifier (`scripts/check_standard_ecdsa_contract.py`)

Checks the *exact* exported theorem types (not just their names), the six-input
count, the fixed-hint contract and the certified cost type, and runs two
deliberately mismatched fixtures:

```
contract: theorem types, input count, hint contract and cost type all check
contract: mismatched cost fixture correctly rejected
contract: mismatched soundness fixture correctly rejected
contract: executable count agrees: allocations=4628 rows=4634 score=9262
contract: all checks passed
```

### 3.2 Matrix export and independent validation

`lake exe standardEcdsaCheck --export=<dir>` writes `rows.txt` (one `A;B;C`
sparse affine form per assertion), `witness.txt` (the 4 634-wire assignment)
and `meta.txt`. `scripts/check_standard_ecdsa_matrices.py` re-checks the data
in Python without trusting Lean:

```
matrices: all 4634 rows satisfied by the exported witness
matrices: the six external inputs are bound to wires 0..5
matrices: every one of the 4628 auxiliary wires is constrained by at least one row
matrices: all checks passed
```

The last line is an exhaustive mutation check: each of the 4 628 auxiliary
wires is incremented and at least one row must break. Matrix export is
documented as **tested tooling**, not as a proved-correct exporter.

### 3.3 Regression suite (`lake exe standardEcdsaTests`, T19)

The oracle is `Tests/StandardECDSA/Oracle.lean`, an independent affine P-256
verifier written from the textbook group law over `ZMod p`; it shares no code
with the circuit or with the vendored Longfellow library. The Longfellow
accept/reject labels are **not** used as the oracle.

46 checks, 0 failures:

* **positive (15)** — baseline; `Q = -G`; `Q + R = O`; `Q = R`; small key;
  `d = n-2`; digest edges `0, 1, n-1, n, p-1, p, p+1, 2^256-1` (the pair `1`
  and `p+1` are distinct digests separated by `p`, hence distinct limb inputs);
  and the **overflow** fixture with `x(V) = n + 3`, i.e. `n ≤ x(R) < p` and
  `overflow = 1`. Each requires the honest prover to succeed, i.e. the offset
  search over the 1 040 candidates must find a good `H` (observed: `H = [1]G`
  or `H = [2]G`).
* **negative (12)** — `r = 0`, `s = 0`, `r = n`, `s = n`, `r = n+1`, `s = n+1`,
  public key off the curve, altered digest, altered signature, verification
  point at infinity (`Q = -[E·r⁻¹]G`), and malformed digest limbs
  (`digestLo = 2^128`, `digestHi = 2^128`). The oracle rejects and the circuit
  rejects for every seed in the sampled seed space.
* **mutations (19)** — the honest seed is accepted; flipping any of the digest
  / `r` / `t` bits (LSB and MSB), `overflow`, `R.y`, `H.x`, `H.y` breaks the
  witness; and incrementing computed wires `6, 100, 1000, 2000, 3000, 4000,
  4633` breaks the witness.

`x = 0` public keys: the plan asks to "certify existence or impossibility rather
than inventing an infeasible fixture". Existence is **certified**:
`Tests.StandardECDSA.Main.xZeroY_sq : xZeroY * xZeroY = params.b` and
`xZeroY_onCurve : onCurve 0 xZeroY = true`, both by `decide`, with
`xZeroY = 46263761741508638697010950048709651021688891777877937875096931459006746039284`.
A *signature* under an `x = 0` key is not constructible without a discrete
logarithm (no `d < 2000` has `x([d]G) = 0`), so no positive fixture is
included; the circuit's handling of `x = 0` is covered by the unconditional
`main_soundness`.

## 4. Toolchain and dependency hashes

| item | value |
|---|---|
| toolchain | `leanprover/lean4:v4.34.0` |
| `clean` | `93c9d1ef45be9f687214625d7857889cf2485504` |
| `mathlib` | `5ed2965256430c3649e86755f9576b54eca72435` |
| branch | `leanstral-with-astra-planner` |

`maxHeartbeats` and `maxRecDepth` are unchanged from the repository defaults;
no axiom was added; there is no `sorry` under `StandardECDSA/`.

## 5. Remaining gaps (honest, no `sorry`)

Three hypotheses remain explicit rather than discharged. None of them is a
`sorry`; each is a clearly-true statement about the concrete circuit that is
not yet proved.

### G1 — T13 instantiation bridge

`CompleteWitness` (`StandardECDSA/Main.lean`) carries the concrete distinct-`x`
denominators (`hfb0`, `hfb`, `hshy`, `hs1…hs5`, `hj1`, `hj2`, `hjf1…hjf4`) as
explicit hypotheses. `Math/OffsetConditions.lean` proves `GoodOffset H hH fam`
for the 1 039-slot family and `Math/OffsetCandidates.lean` proves
`exists_goodOffset`, but the step `GoodOffset H hH fam → (concrete denominators
≠ 0)` is not yet formalised. **Obstruction:** the concrete denominators are
`Operations.localLength`-offset expressions over the nine-stage split, so the
bridge needs the same `_ops`-rewriting discipline used for the cost
certificates, applied to `Expression.eval` rather than `operationCount`.

### G2 — T16 concrete witness environment

`main_completeness` takes `∃ env, UsesLocalWitnessesCompleteness ∧
CompleteWitness` as a hypothesis. The *seed* half is proved
(`Witness.generateSeed_complete`), but the concrete 4 634-wire
`ProverEnvironment` is not yet constructed inside Lean. **Obstruction:** the
environment must be built from `FlatOperation.witgen` and then shown to satisfy
`UsesLocalWitnessesCompleteness`; the honest-prover facts are available
executably (`lake exe standardEcdsaTests` exercises exactly this path) but the
Lean-level construction is not done.

### G3 — `NoLookupSub`

`main_accepts_iff_standard` takes `hl : ((main inp).operations n).shallowLookups
= []` and `hs : ((main inp).operations n).subcircuits = []`. Both are true by
construction (the circuit never uses `Circuit.lookup` or `Circuit.subcircuit`),
but they are not yet proved.

**Obstruction (diagnosed, not worked around).**

1. `Operations.shallowLookups` and `Operations.subcircuits` have no
   `@[circuit_norm]` lemmas in `clean` (only `subcircuits_nil/assert/witness/
   lookup/interact/subcircuit/append` exist, and nothing at all for
   `shallowLookups`).
2. `simp [circuit_norm, main_ops]` on the concrete 4 634-operation list blows
   up: the goal retains the whole nine-stage `Operations.localLength` nest, and
   the `main_ops` rewrite leaves `sorry`-shaped metavariables in the offsets.
3. The compositional route needs a `NoLookupSub` predicate mirroring the
   `CostIs` API (`pure`/`bind`/`map`/`witnessField`/`assertZero`/
   `mapFinRange`/`foldlRange`/`append`). The phase level is free — the `_ops`
   lemmas (`seedPhase_ops`, `curvePhase_ops`, …, `main_ops'`) already exist —
   but the gadget level is not: `ExplicitCircuit` gives
   `operations := fun n => (g n).2` for `isOnCurve`, `pointEquality` and
   `assertZeroLazy`, i.e. *no explicit operation list*, so `NoLookupSub` for
   `assertZeroLazy` must be proved by induction on the expression structure,
   mirroring `azlLen`/`azlLoopCost`. (`mat` is fine: `matOps` is explicit and
   manifestly `.witness`/`.assert`-only.)

So closing G3 means redoing, for a second predicate, the same
induction-on-expression work that the cost certificates already do. It is
mechanical but not small, and it was not completed in this round.

## 6. Release summary

* **Score: 4 628 allocations + 4 634 rows = 9 262**, certified by
  `StandardECDSA.main_cost` and reproduced by `lake exe standardEcdsaCheck`.
* **Proof roots:** `main_soundness`, `main_complete_with_seed`,
  `main_completeness`, `main_accepts_iff_standard`, `main_cost` — all referring
  to the actual circuit `main`, all axiom-clean.
* **Audit roots:** 30 theorems, audited fail-closed by
  `scripts/check_standard_ecdsa_axioms.py`.
* **Explicit build targets** (the release check is *not* the default
  `lake build` alone):

  ```sh
  lake build StandardECDSA.Main StandardECDSA.Cost
  lake build Tests.StandardECDSA.Axioms
  lake exe standardEcdsaCheck --count-only
  lake exe standardEcdsaCheck --export=/tmp/ecdsa_export
  lake exe standardEcdsaTests
  python3 scripts/check_standard_ecdsa_axioms.py
  python3 scripts/check_standard_ecdsa_contract.py
  python3 scripts/check_standard_ecdsa_matrices.py /tmp/ecdsa_export
  ```

* **Validation scope:** the arithmetic relation and the exact 256-bit digest
  binding are proved for the actual circuit; the executable suite validates the
  circuit against an independent standard verifier on 46 fixtures; the matrix
  export is validated independently but is documented as tested tooling.
* **Remaining assumptions:** G1, G2, G3 above.
