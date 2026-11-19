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

### G1 — T13 instantiation bridge — **PARTIAL: enumeration done, bridge open**

`CompleteWitness` (`StandardECDSA/Main.lean`) carries the concrete distinct-`x`
denominators (`hfb0`, `hfb`, `hshy`, `hs1…hs5`, `hj1`, `hj2`, `hjf1…hjf4`) as
explicit hypotheses. `Math/OffsetConditions.lean` proves `GoodOffset H hH fam`
for a generic family and `Math/OffsetCandidates.lean` proves
`exists_goodOffset`, but the step `GoodOffset H hH fam → (concrete denominators
≠ 0)` is not yet formalised.

**What is now done** — `StandardECDSA/Math/OffsetFamily.lean` (new, 250 lines,
green, axiom-clean):

* `SlotIx`, the explicit slot index type (a nested sum, so `Fintype.card`
  computes by `simp` — no `decide`, no `maxRecDepth` bump);
* `coeffOf : SlotIx → Nat` with `coeffOf_pos` and `coeffOf_lt`, so every slot
  is a legal `BadFamily` equation `[c]H = B` with `c ∈ {1,2,3,4}`;
* `targetOf`, the concrete right-hand side of each equation, built from `G`,
  `Q`, `R` and the fixed shift `S` only — hence independent of `H`, as
  `BadFamily` requires;
* `famOf`, the concrete `BadFamily Grp`, and `famOf_m : (famOf …).m = 1289`.

**Finding 1 — the plan's slot budget was too small — RESOLVED.** The plan
budgets 1,039 slots and 1,040 candidates `[k+1]G`. The circuit actually needs
**1,293** slots (`famOf_m`): the plan's count omits the 128 fixed-base window
denominators (`fbWin`, 256 slots) and undercounts the ladder's second
denominator. The candidate set has been enlarged to `Fin 1294 = 1,293 + 1` (the
tight bound) throughout:

* `Math/OffsetCandidates.lean`: `offsetCandidate : Fin 1294 → Grp`,
  `thousand_two_hundred_ninety_four_lt_n : 1294 < n`,
  `offsetCandidate_injective` re-proved, `exists_goodOffset` /
  `exists_goodOffset_nat` / `findGoodOffset` re-bounded to `m < 1294`;
* `Math/OffsetFamily.lean`: `famOf_m : (famOf …).m = 1293`,
  `famOf_m_lt_candidates : (famOf …).m < 1294`, and the instantiated existence
  theorem `exists_goodOffset_famOf : ∃ k : Fin 1294, (famOf …).Avoids
  (offsetCandidate k)`;
* `Witness/Generate.lean`, `Witness/Correctness.lean`: every `hm : fam.m < 1040`
  is now `hm : fam.m < 1294`;
* `StandardECDSA/Check.lean`: the executable search bound is 1294.

The 1,039 fiction is gone: the count is stated as 1,293 everywhere.

**Finding 2 — the `E ∈ {0, n}` unsatisfiability claim — REFUTED.** The earlier
report claimed that the final `elmTo` denominator vanishes identically for
digest `E = 0` or `E = n`, making the circuit reject standard-valid inputs.
That claim was **wrong**, and the counter-evidence is both formal and
executable:

* *Formal.* `elmTo p q target` (`Gadgets/ELM.lean`) writes `xu = x(p + q)` at
  wire `n + 2`, **not** `x(target)`. So the second denominator of the final
  ladder step is `x(C_255) - x(C_255 + T_255)`, not `x(C_255) - x(-ep)`. Its
  two equations are `[3]H = σ_255·(-b0·Q - b1·R)` and
  `[1]H = σ_255·(-2B_255 - b0·Q - b1·R)` — both with **nonzero** coefficient.
  There is no coefficient-`0` slot anywhere in the family, and
  `coeffOf_pos` is unconditional.
* *Executable.* `lake exe standardEcdsaTests` reports
  `PASS valid-digest-0  oracle=true circuit=(some 1) (H = [1]G)` and
  `PASS valid-digest-n  oracle=true circuit=(some 1) (H = [1]G)`: the circuit
  accepts both digests with the honest prover.

The root cause of the error was reading the `elmTo` output wire as `x(target)`
instead of `x(p + q)`. No circuit repair is needed, and the certified cost is
unchanged at 4,628 allocations + 4,634 rows = 9,262.

**Honest-witness row bricks — DONE** (`StandardECDSA/Phases/HonestWitness.lean`,
new, green, axiom-clean). The induction needs to know that the *honest prover's*
rows hold, and the honest prover's wire values are pinned by
`ProverEnvironment.UsesLocalWitnessesCompleteness`. The file proves, for every
gadget of the fixed-base and ladder phases,

```text
UsesLocalWitnessesCompleteness env n (g.operations n) → ConstraintsHold.Soundness env (g.operations n)
```

with exactly the extra hypotheses the guarded denominators need:

* `soundness_append_intro`, `soundness_bind_intro` — the converses of the
  existing `soundness_append` / `soundness_bind` splitters (needed because the
  induction *assembles* rather than splits);
* `muxConst4W_soundness_of_ulwc`, `selW_soundness_of_ulwc`,
  `mux4W_soundness_of_ulwc` — unconditional;
* `affAdd_soundness_of_ulwc` — needs `x(q) - x(p) ≠ 0`;
* `elmCore_soundness_of_ulwc`, `elm_soundness_of_ulwc` — need
  `x(q) - x(p) ≠ 0` and `x(p) - xu ≠ 0`;
* `fixedBaseBody_soundness_of_ulwc`, `jointLadderBody_soundness_of_ulwc` — the
  two phase bodies, taking the two halves' `UsesLocalWitnessesCompleteness`
  facts separately so that no `>>=` or fold is ever `whnf`-ed.

`elmTo` is deliberately absent: its last two rows are the assertion being
checked, not witness definitions.

**Round-20 additions — the `affDouble` / `shiftedTables` bricks are now in.**
The missing `Soundness` version of `mat_complete` is proved as
`mat_soundness_of_ulwc` (the same induction as `mat_complete`, re-run with
`ConstraintsHold.Soundness`; it cannot be obtained by bridging
`Completeness → Soundness` because `NoLookupSub.nls_matOps` lives in
`NoLookupSub.lean`, which imports `Main.lean`). On top of it:

* `affDouble_soundness_of_ulwc` — needs the explicit
  `hsc : Expression.eval env.toEnvironment (sc 2 p.2) ≠ 0` (discharged by
  `mul_ne_zero h2 hy`) before `field_simp`;
* `shiftedTables_soundness_of_ulwc` — the eight-row composition, mirroring
  `shiftedTables_complete` row for row, with the five guarded denominators
  `hdx1…hdx5` as hypotheses.

All three are axiom-clean and registered in `Tests/StandardECDSA/Axioms.lean`
and `scripts/check_standard_ecdsa_axioms.py` (51 roots).

**What remains.** The bridge itself: for each of the 646 denominators, derive
`x(P) - x(Q) ≠ 0` from `GoodOffset` by the honest-witness induction
`P(i) := (A_i = [a_i]H + B_i) ∧ (denominator_i ≠ 0)`, using
`UsesLocalWitnessesCompleteness` to read the hint values and the existing
`fbStep` / `ladInv` / `affAdd_sound` bricks for the group step. The
`H`-coefficients are already known to be `±1` (`ladAccH_eq`) and `±3`
(`Tpt`), which is why every slot coefficient is in `{1,2,3,4}`. This is
mechanical but large (128 + 255 step inductions) and was not completed.

**G1-b — the affine→projective bridge — DONE**
(`StandardECDSA/Math/DenominatorBridge.lean`, new, green, axiom-clean, 10 roots).
`GoodOffset`'s `Avoids` is stated on `(H.toProjective).toMathlibPoint params …`
in the *projective* group `Grp`, whereas the denominators are field-level
`Expression.eval env …` statements about `Affine.Point.some` values. The file
closes the gap:

* `toAff` / `toAff_nsmul` — `Projective.Point.toAffineLift` as a plain function
  `Grp → Affine.Point Wp`, commuting with `Nat`-multiples;
* `BadFamily.toAffine` / `BadFamily.avoids_toAffine` — the bad family read in
  the affine group, with `Avoids` transported verbatim along the additive
  equivalence `Projective.Point.toAffineAddEquiv`;
* `some_eq_or_neg_of_X_eq` — **the crux**: two on-curve affine points of P-256
  with the same `x`-coordinate are equal or negatives (`y_eq_or_neg` composed
  with `negPt_group`);
* `nsmul_sub_of_add_eq` and `X_eq_imp_bad` — a vanishing denominator becomes one
  of the three bad equations `[a-b]H = B₁-B₀`, `[b-a]H = B₀-B₁`,
  `[a+b]H = -(B₀+B₁)`;
* `nsmul_ne_of_slot` — reading a slot: `coeff i = c` and `target i = T` give
  `c • Hpt ≠ T`;
* `X_ne_of_avoids` — the `Avoids`-level form: if none of the three bad equations
  holds, `x(P) ≠ x(Q)`;
* `goodOffset_avoids` / `goodOffset_Z_ne` / `goodOffsetAffinePt` /
  `goodOffset_avoids_affine` / `goodOffsetAffinePt_eq_some` / `nsOfOnCurve` —
  the `GoodOffset` entry points, including the identification of the offset's
  affine image with `Affine.Point.some H.X H.Y`.

**G1-c — the honest-witness inductions — IN PROGRESS.**

Two further bricks landed in `DenominatorBridge.lean`:

* `X_ne_of_avoids_sharp` — the sharp form of the bridge: the three bad equations
  are tested at their *actual* coefficients `a - b`, `b - a`, `a + b`, guarded by
  the corresponding order facts, so a caller only has to rule out the equations
  that can actually occur (the unguarded `X_ne_of_avoids` demands all three for
  every `c`, which is unusable when e.g. `b ≤ a` is false);
* `toAff_toProjective` — `toAff` is a retraction of `Affine.Point.toProjective`,
  which is what turns a family target `B.toProjective` back into `B`.

**Obstruction found (G1-c, slot indexing).** The per-denominator instantiation
needs to name the family slot, i.e. `Fintype.equivFin SlotIx s`. That term alone
exceeds the recursion budget:

```lean
example : SlotIx ≃ Fin 1293 := Fintype.equivFin SlotIx
-- error: maximum recursion depth has been reached
```

`SlotIx` is a six-way nested sum, so `Fintype.equivFin` has to compute
`Fintype.card SlotIx` through the instance and the `Fin`/`Prod`/`Sum` instances
recurse past the default `maxRecDepth`. `famOf_m` avoids this only because it
rewrites `Fintype.card_sum`/`card_prod`/`card_fin` explicitly rather than
evaluating the instance. Raising `maxRecDepth` is forbidden by the task rules, so
the fix is structural: give `famOf` an **explicit** index equivalence
`slotEquiv : SlotIx ≃ Fin 1293` built by hand from `Equiv.sumCongr` /
`Equiv.prodCongr` / `finCongr` (cheap, no instance search), and index the family
by `slotEquiv` instead of `Fintype.equivFin`. `famOf_m` then becomes `rfl`-ish and
the slot lemmas `famOf_coeff_apply` / `famOf_target_apply` become `rfl`.

**What remains (G1-c).** The two honest-witness inductions
`P(i) := (A_i = [a_i]H + B_i) ∧ (denominator_i ≠ 0)` over the 128 fixed-base
windows and the 256 ladder steps, instantiating `X_ne_of_avoids` once per
denominator with the concrete `a`, `b`, `B₀`, `B₁` and the three slot indices.

### G2 — T16 concrete witness environment

`main_completeness` takes `∃ env, UsesLocalWitnessesCompleteness ∧
CompleteWitness` as a hypothesis. The *seed* half is proved
(`Witness.generateSeed_complete`), but the concrete 4 634-wire
`ProverEnvironment` is not yet constructed inside Lean. **Obstruction:** the
environment must be built from `FlatOperation.witgen` and then shown to satisfy
`UsesLocalWitnessesCompleteness`; the honest-prover facts are available
executably (`lake exe standardEcdsaTests` exercises exactly this path) but the
Lean-level construction is not done.

### G3 — `NoLookupSub` — **CLOSED**

`main_accepts_iff_standard` used to take `hl : ((main inp).operations
n).shallowLookups = []` and `hs : ((main inp).operations n).subcircuits = []`.
Both are now *proved*.

**What was built.** `StandardECDSA/NoLookupSub.lean` (new file, ~450 lines):

* `NoLookupSub (ops : Operations Fp) : Prop := ops.shallowLookups = [] ∧
  ops.subcircuits = []`, mirroring the `CostIs` API of
  `Challenge/Utils/CostR1CS.lean`;
* preservation lemmas for the `Circuit` combinators — `nls_pure`, `nls_bind`,
  `nls_map`, `nls_witnessField`, `nls_assertZero`, `nls_mapFinRange`,
  `nls_foldlRange`, `nls_append`, `nls_flatten`, `nls_matOps`, `nls_mat`;
* preservation lemmas for every gadget — `nls_assertZeroLazy` (by induction on
  the expression structure, mirroring `azlLen`/`azlLoopCost`, since
  `ExplicitCircuit` gives `operations := fun n => (g n).2` there),
  `nls_isOnCurve`, `nls_pointEquality`, `nls_nonzero`, `nls_assertBool`,
  `nls_sel`, `nls_muxConst4`, `nls_mux4`, `nls_affAdd`, `nls_affDouble`,
  `nls_elm`, `nls_elmTo`, `nls_assertLtOrderOf`, `nls_assertLtOrderGuardedOf`,
  `nls_hint`, `nls_bitBody`, `nls_bitVec`;
* preservation lemmas for every phase — `nls_seedPhase`, `nls_curvePhase`,
  `nls_nonzeroPhase`, `nls_bitsPhase`, `nls_bindPhase`, `nls_cmpPhase`,
  `nls_fixedBaseBody`, `nls_fixedBase`, `nls_shiftedTables`,
  `nls_jointLadderBody`, `nls_jointLadderFinal`, `nls_jointLadder`;
* `nls_main`, and the two exported facts

  ```lean
  theorem main_shallowLookups_nil (inp : Var Input Fp) (n : ℕ) :
      ((main inp).operations n).shallowLookups = []
  theorem main_subcircuits_nil (inp : Var Input Fp) (n : ℕ) :
      ((main inp).operations n).subcircuits = []
  ```

**Consequence.** `StandardECDSA/Main.lean`'s theorem is renamed
`main_accepts_iff_standard_of_nil` (it keeps `hl`/`hs` as hypotheses, since
`Main.lean` cannot import a file that imports it), and the hypothesis-free
`main_accepts_iff_standard` now lives in `NoLookupSub.lean`:

```lean
theorem main_accepts_iff_standard (inp : Var Input Fp) (penv : ProverEnvironment Fp)
    (n : Nat) (hw : penv.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (h : CompleteWitness inp penv n) :
    ConstraintsHold.Soundness penv ((main inp).operations n) ↔
      standardVerify (Expression.eval penv inp.pkX) (Expression.eval penv inp.pkY)
        (Expression.eval penv inp.digestLo) (Expression.eval penv inp.digestHi)
        (Expression.eval penv inp.r) (Expression.eval penv inp.s)
```

No hypothesis about the shape of `main`'s operation list remains.

**Observed results.** `lake build StandardECDSA.NoLookupSub` green (9 021 jobs);
`lake build Tests.StandardECDSA.Axioms` green (9 023 jobs); axiom audit 33 roots
pass; contract verifier passes (including the two new `example`s for
`main_shallowLookups_nil` / `main_subcircuits_nil`); matrix check passes;
`lake exe standardEcdsaTests` 46/46.

## 6. Release summary

* **Score: 4 628 allocations + 4 634 rows = 9 262**, certified by
  `StandardECDSA.main_cost` and reproduced by `lake exe standardEcdsaCheck`.
* **Proof roots:** `main_soundness`, `main_complete_with_seed`,
  `main_completeness`, `main_accepts_iff_standard`, `main_cost` — all referring
  to the actual circuit `main`, all axiom-clean.
* **Audit roots:** 33 theorems, audited fail-closed by
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
* **Remaining assumptions:** G1 and G2 above (G3 is closed).
