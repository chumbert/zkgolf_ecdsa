# Proof plan: certified projected-signature ECDSA circuit at ≤ 9,500

Status: plan, 17 November 2026. Branch `circuit_baseline` (commit `3a1bd20`).
Scope: turn the experimental circuit `Baseline/Projected/Offset.lean` (measured
**9,267 = 4,631 allocations + 4,636 rows**) into a fully proved submission:
soundness, completeness, exact cost, R1CS shape, witness-IR, computable witnesses,
lawful channels. Budget: **9,500**, i.e. **233 points of slack** for any constraint
the proofs force us to add.

The plan is written as self-contained task briefs (§6–§11) that can be handed to
subagents. §1–§5 are shared context every subagent should read first.

---

## 1. What exists and what is missing

### 1.1 The circuit (`Baseline/Projected/Offset.lean`)

Inputs (free, not scored): `pkX, pkY, digest, r, s : F_p`.
Hint rows (`hint i` = `.hintGet "offset" 1 (const i) 0`):
`0 = ry`, `1,2 = H = (hx,hy)`, `3..10 = pre[0..7]`, `11+3i, 12+3i, 13+3i = (e_i, r_i, t_i)`
for `i = 0..255` (LSB first, weight `2^i`).

Constraint groups and their cost (derived from the code; the per-group total matches
the measured 9,267 exactly — T0.2 must re-confirm with the counter):

| # | Group | What it enforces | alloc | rows | score |
|---|---|---|---:|---:|---:|
| A | hints `ry, hx, hy` | – | 3 | 0 | 3 |
| B | `isOnCurve` ×3 (Q, R=(r,ry), H) | affine curve eq. | 6 | 9 | 15 |
| C | `nonzero` ×3 (`pkX`, `r`, `n−s`) | inverse exists | 3 | 3 | 6 |
| D | `originalTable` (8 hints + 4 Longfellow `addE` + `pointEquality`) | `ValidPreComputationExact` | 37 | 37 | 74 |
| E | bits: 768 hints + 768 `assertBool` + 3 recomposition rows | `Σe_i2^i=digest`, `Σr_i2^i=r`, `Σt_i2^i=n−s` | 768 | 771 | 1,539 |
| F | `assertLtOrder` ×2 (34 zero-runs each) | `R ≤ n−1`, `t ≤ n−1` | 68 | 68 | 136 |
| G | fixed base: `affAdd(H, −S)` + 128 × (`muxConst4` + `affAdd`) | `ep = H + E·G` | 644 | 644 | 1,288 |
| H | offsets: `affDouble(H)`, `affAdd(2H,H)`, 6 × `affAdd(±3H, X)` | `±3H, ±3H+Q, ±3H+R, ±3H+QR` | 32 | 32 | 64 |
| I | ladder: 255 × (`mux4` + `elm`) + final (`mux4` + `elmTo`) | `2acc+T` chain, final `= −ep` | 3,070 | 3,072 | 6,142 |
| | **Total** | | **4,631** | **4,636** | **9,267** |

(D's split: 8 hint allocs + 29 product allocs, 37 rows. D = 74 is also the handoff's
"remove table checks −74" figure, a useful cross-check.)

Group equation checked: with `acc₀ = −H`, step `j` (MSB first, `i = 255−j`) uses the
`plus` table (`+3H + X`) for even `j` and `minus` (`−3H + X`) for odd `j`, where
`X ∈ {O, Q, R, Q+R}` is selected by `(r_i, t_i)`. Then `acc₂₅₆ = rQ + tR − H` and the
final row forces `acc₂₅₆ = −ep = −H − E·G`, i.e.

```
E·G + r·Q + t·R = O,   t = n − s,   R = (r, ry)
```

### 1.2 Proofs already done (no `sorry`, standard axioms)

| File | Content | Used by |
|---|---|---|
| `Projected/BoundLF.lean`, `NaturalBoundLF.lean`, `RepresentationIndependent.lean` | `BoundLF ↔ RepresentationIndependentLF` (generic field) | spec bridge |
| `Projected/P256Bridge.lean` | `p256_boundLF_iff_representation_independent` + instances `IsElliptic`, `CurveHasNoPointsOfOrder2`, `NeZero k` for `K` | M1 |
| `Projected/Algebra.lean` | ELM identities, `affine_add_onCurve`, `elm_second_denominator_ne`, `double_denominator_ne`, `elm_output_onCurve`, `affine_double_onCurve` | G3–G5 |
| `Projected/AffineBridge.lean` | `affine_add_eq_group`, `affine_double_eq_group`, `elm_eq_group` (Mathlib group law) | G3–G5 |
| `Projected/ProjectiveBridge.lean` | same, to Longfellow `addE`/`doubleE` via `ProjectiveEquiv` | M1/M7 |
| `Projected/OffsetExistence.lean` | `exists_avoiding_injective_equations` (generic counting) + collision identities | M3 |
| `Projected/P256Algebra.lean` | `two_ne_zero`, `discriminant_ne_zero` over `Fp` | gadgets |
| `OptimizationLemmas.lean` | `quotient_gate`, `gatedBits_correct` (Bool level) | M4 |
| `vendor/longfellow/ECDSA/ECBridge.lean` | `toMathlibPoint_add/double/bsmul`, `addE_on_curve`, `toMathlibPoint_eq_iff_ProjectiveEquiv`, … | M1, M7 |

### 1.3 Missing (this plan)

1. A **trusted contract** for the projected interface (the current pointwise
   challenge cannot be met by this circuit: it ignores `int_x/y/z`).
2. A **proof-friendly refactor** of the circuit (gadgets as Clean subcircuits,
   Clean loop combinators, literal constant tables) with unchanged cost.
3. Constant-table and small-order **certificates** for P-256.
4. Gadget-level soundness/completeness, loop invariants, top-level assembly.
5. The **offset-existence instantiation** (completeness for every valid input).
6. The five structural obligations (cost, R1CS, IR, computable witnesses, channels).

---

## 2. Key design decisions (decide before dispatching)

**D1 — Specification (recommended: Track A).** The trusted spec for 5 field inputs:

```lean
-- Challenge/Specs/ECDSAP256Projected.lean (trusted; imports only vendor + ECDSAP256)
def Spec (pkX pkY digest r s : K) : Prop :=
  ∃ w : EcdsaWitness K,
    ValidEcdsaWitness w { X := pkX, Y := pkY } digest n params ∧
    natR (w.bi.map val3) = r.val ∧ n - natS (w.bi.map val3) = s.val
```

This is `RepresentationBridge.BoundLF` with `r.val, s.val`: the existential projection
of the *unchanged* Longfellow relation that binds the actual signature `(r, s)`. Its
trusted base is only the vendored Longfellow definitions already in the challenge.
The proofs work with the equivalent `RepresentationIndependentLF` / a Mathlib group
form (task M1).

*Track B* ("does not need to follow Longfellow"): full standard ECDSA
(`r = R.x mod n`, no table exclusions, `pkX = 0` allowed). Needs circuit changes
(estimated ≈ 9,26x, unmeasured) and a new spec. Treated as an optional extension
(§11) once Track A is green; most of the gadget and ladder work carries over.

**D2 — Completeness hint.** Clean's `Completeness` quantifies over the prover's
hint, so `ProverAssumptions` must pin it. Recommended (non-vacuous):

```lean
def ProverAssumptions (input) (_data) (hint) : Prop :=
  Spec input.pkX input.pkY input.digest input.r input.s ∧ hint = Solution.honestHint input
```

with `Solution.honestHint : Input K → ProverHint K` supplied by the submission
(classical choice allowed; it is not executed by the verifier). Because `honestHint`
is a *function of the input only*, completeness cannot smuggle in "assume H is good":
the existence of a good offset is forced into the completeness proof (task M3).
Rejected alternative: `Spec ∧ HintGood hint` — would need a separate
"`HintGood` is satisfiable" obligation and leaks circuit details into the trusted file.

**D3 — Assumptions** `:= True`; **ProverSpec** `:= True`; **Output** `:= unit`.

**D4 — Refactor policy.** Proofs target a refactored circuit `Projected.Circuit.main`
(task T0.2), not `Offset.main`. Its score must be **exactly 9,267** unless a proof
task documents a forced change; any increase is charged against the 233 slack and
must be approved in `docs/ecdsa-proof-plan.md` §12 (decision log).

**D5 — No full unfolding.** No proof may `simp`/`decide` through the whole circuit.
Top-level `main` must be ~15 subcircuit/loop calls; each gadget's `ConstraintsHold`
is consumed through its proved `Spec`.

---

## 3. Ground rules for every subagent

* Work only on branch `circuit_baseline` (or a worktree off it). **Do not read other
  branches.** Do not modify `Challenge/Specs/ECDSAP256.lean`, the existing pointwise
  instance, `Challenge/Utils/*.lean`, or `vendor/` (except where a task says so).
* Toolchain: Lean `v4.34.0`, Clean `93c9d1ef…`, Mathlib `5ed29652…` (see `lakefile.lean`).
  Run `scripts/bootstrap.sh` once if `.lake/` is missing.
* No `sorry` in verified proof paths. For a blocked, uncommitted draft only,
  follow §13. No `native_decide`, no `axiom`, no `implemented_by` in proof paths.
  Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`. Check with
  `#print axioms` (pattern: `Baseline/Projected/Audit.lean`, `scripts/check_axioms.py`).
* Big-number computation in the kernel: state certificates over **`Nat`** (`% p`)
  and close with `decide`/`Nat.decEq` (GMP-accelerated), not `decide` on `ZMod p`
  instances. Raising `maxHeartbeats`/`maxRecDepth` locally is fine; report build time.
* A verified task ends with: the file(s) listed under *Deliverable*, a green
  `lake build <module>`, an axiom print, and a short note of statement changes made
  to frozen interfaces (should be none without approval).
* New proof code lives under `Solution/Projected/` (new `lean_lib SolutionProjected`
  in `lakefile.lean`, added by T0.2). Namespace `Solution.Projected`.

Common abbreviations below: `K = Fp = ZMod p`, `W = params.toMathlib.toAffine`,
`pt x y h := Affine.Point.some x y (short_nonsingular params x y h)` (point of
`W.Point`), `G := pt gx gy _`.

---

## 4. Target module layout

```
Challenge/Specs/ECDSAP256Projected.lean                 (T0.1, trusted)
Challenge/Instances/ECDSA_P256_Projected/
    Interface.lean  Challenge.lean  Cost.lean           (T0.1, trusted template)
configs/ECDSA_P256_Projected.json                        (T0.1)
Solution/Projected/
    Types.lean          Point/Table structs (ProvableStruct)         T0.2
    Gadgets.lean        nonzero, mulWire, assertBool, affAdd, affDouble,
                        elm, elmTo, mux4, muxConst4, isOnCurve        T0.2
    Constants.lean      literal fixed tables + shift (generated)      T0.3
    Circuit.lean        main (refactored), honest witness generators  T0.2
    Hint.lean           honestHint                                    C5
    Math/GroupSpec.lean        M1
    Math/ConstantCerts.lean    M2 (+ generated Certs/*.lean)
    Math/OffsetGood.lean       M3
    Math/Comparator.lean       M4
    Math/Bits.lean             M5
    Math/Ladder.lean           M6
    Math/LongfellowTable.lean  M7
    Proof/Gadget*.lean         G1–G9
    Proof/FixedBase.lean       C1
    Proof/Ladder.lean          C2
    Proof/Soundness.lean       C3
    Proof/Completeness.lean    C4
    Proof/Cost.lean  R1CS.lean  IR.lean  Witness.lean  Channels.lean   O1–O5
    Submission.lean            F1 (fills the template)
scripts/gen_projected_constants.py   T0.3/M2
```

---

## 5. Dependency graph and waves

```
Wave 0 (parallel):  T0.1  T0.2  T0.3  M1  M2  M4  M5  M6  M7
                      │     │     └──┬──┘
Wave 1 (parallel):    │    G1..G9  M3(needs T0.2 catalogue + M2)   O1 O2 O3 O5
Wave 2:               │    C1  C2  (soundness loops)   C5 (honestHint)  O4
Wave 3:               │    C3 (soundness)   C4 (completeness)
Wave 4:               └──► F1 (assembly, audit, comparator, docs)
Optional:                  B1..B4 (Track B)
```

Critical path: **T0.2 → G5/G6 → C2 → C3/C4 → F1**. M2 (certificates) and M3
(offset existence) are the main mathematical risks; start them in Wave 0/1.

Size legend: S < ½ day, M ≈ 1 day, L ≈ 2–3 days, XL > 3 days (agent-time estimates).

---

## 6. Wave 0 — contract, refactor, constants

### T0.1 Trusted projected contract (S) — *needs user sign-off on D1/D2*

**Read:** `Challenge/Specs/ECDSAP256.lean`, `Challenge/Instances/ECDSA_P256_Digest/*`,
`configs/ECDSA_P256_Digest.json`, `scripts/check_comparator.py`, `Baseline/Projected/BoundLF.lean` (def `BoundLF`).
**Deliver:**
* `Challenge/Specs/ECDSAP256Projected.lean`: `Spec` exactly as in D1, importing only
  `ECDSA.EcdsaCircuit`, `ECDSA.Pratt`, `Challenge.Specs.ECDSAP256`.
* `Interface.lean`: `structure Input (F) where pkX pkY digest r s : F deriving ProvableStruct`,
  `Output := unit`, `Assumptions := True`, `Spec`, `ProverAssumptions` per D2
  (references `Solution.ECDSA_P256_Projected.honestHint`, declared `sorry` in the
  template like `main`), `ProverSpec := True`.
* `Challenge.lean`: copy of the digest template with the 7 obligations (+ `honestHint`
  placeholder). `Cost.lean` placeholders `0`.
* Config JSON + comparator entry mirroring the digest instance.
**Accept:** `lake build Challenge` green with template `sorry`s; a one-line lemma in
`Tests/` showing `Spec` unfolds to `RepresentationBridge.BoundLF ⟨pkX,pkY⟩ digest r.val s.val n params`
(proved by `Iff.rfl`/`rfl`, placed in the untrusted side).
**Pitfall:** do not import any `Baseline/` module from trusted files.

### T0.2 Proof-friendly circuit refactor + interface freeze (L) — critical path

**Read:** `Baseline/Projected/Offset.lean`, `Baseline/Circuit.lean` (`mat`, `mm`, `pm`,
`addE`, `isOnCurve`, `pointEquality`, `assertZeroLazy`), `Baseline/Optimized.lean`
(`sel`, `assertBool`, `assertLtOrder`, `boundRuns`), `Challenge/Utils/CostR1CS.lean`
(`CostIs.*`), Clean: `Circuit/Loops.lean` (`foldlRange`, `mapFinRange`,
`ConstantLength`), `Circuit/Subcircuit.lean` (`subcircuit`, `subcircuitWithAssertion`).
**Goal:** a new `Solution.Projected.main : Var Input K → Circuit K (Var unit K)` that
is *semantically and cost-identical* to `Offset.main` but provable:
1. `Types.lean`: `structure Point (F) where x y : F deriving ProvableStruct`;
   `Table4` (4 points); inputs of each gadget as ProvableStructs.
2. `Gadgets.lean`: every gadget is a `GeneralFormalCircuit` (or `FormalCircuit` /
   `FormalAssertion` where Assumptions are harmless) invoked via
   `subcircuit`/`subcircuitWithAssertion`/`assertion`. Replace the generic recursive
   `mat` with explicit `mulWire a b := do let w ← witnessField (.mul a b); assertZero (a*b - w); pure w`
   so gadgets have no recursion. Gadget list and **frozen Specs** (statement shapes
   that G-tasks will prove; written with `sorry` proofs here):
   * `nonzero x` → Spec `x ≠ 0`; completeness: `x ≠ 0`.
   * `bit3 i` (3 hint wires + 3 `assertBool`) → Spec bits ∈ {0,1}.
   * `isOnCurve (x,y)` → Spec `y^2 = x^3 + a x + b`.
   * `affAdd P Q` → Spec: `P,Q` on curve ⇒ `Q.x ≠ P.x` ∧ out on curve ∧
     `pt out = pt P + pt Q`. Completeness assumption: `P,Q` on curve, `Q.x ≠ P.x`.
   * `affDouble P` → `pt out = 2 • pt P` (on-curve assumption).
   * `elm A T` → `pt out = 2 • pt A + pt T`; `elmTo A T target` (assertion) →
     `pt target = 2 • pt A + pt T`. Completeness: `T.x ≠ A.x` and `2A+T ≠ O`.
   * `mux4 b0 b1 P0..P3`, `muxConst4 i b0 b1` (table index `i : Fin 128` as a
     parameter, constants from `Constants.lean`) → Spec: bits boolean ⇒ out = selected entry.
   * `originalTable Q R pre` (assertion) → Spec `ValidPreComputationExact`-shaped
     (exact form fixed by M7).
   * `ltOrder bits` (assertion) → Spec `Σ bits·2^k ≤ n−1` (Nat).
3. Loops via `Circuit.mapFinRange 256` (bits), `Circuit.foldlRange 128` (fixed base,
   state = `Point`), `Circuit.foldlRange 127` over a **double step** (plus-step then
   minus-step; body constant length) for ladder steps `j = 0..253`, then step 254
   (plus, `elm`) and the final step 255 (minus, `elmTo`) peeled. Check the index
   map `i = 255 − j` carefully.
4. Keep the hint row layout of §1.1 so `Check.lean`'s `hintValues` still applies;
   allocate the 8 `pre` hints at top level and pass them to `originalTable`.
5. Point `Baseline/Projected/Check.lean` (copy to `Solution/Projected/Check.lean`)
   and `Export.lean` at the new main; add `lean_exe projected2`.
6. **Exception catalogue**: write `docs/projected-exceptions.md` listing every
   witness-generation division in the honest prover (gadget, operands, the group
   condition under which it is 0). Starting point (verify against the code):
   fixed base `H ≠ ±S` (2) and `ep_i ≠ ±T_i` (256); offsets `3H ≠ O` (1),
   `3H ≠ ±X` for `X ∈ {Q,R,Q+R}` (6); ladder first denominators `T_j ≠ ±acc_j`
   (512, coefficients 4 and 2 on H), intermediate results `acc_{j+1} ≠ O` for
   `j < 255` (255, coefficient 1). ≈ 1,032 conditions, each `a•H ≠ B` with
   `a ∈ {±1,±2,±3,±4}` and `B` independent of `H`. Second ELM denominator and the
   doubling denominator need no condition (proved redundant). Reconcile with the
   `m = 1039` comment in `OffsetExistence.lean`.
**Accept:**
* `lake exe projected2 --count-only` prints `allocations=4631 rows=4636 score=9267 R1CS violations=0`;
  full run: 252 vectors agree (166/86), `p+1` digest lift, `Q=3G,R=2G` retry case;
  `python3 Baseline/Projected/check_matrices.py <export dir>` passes.
* Every gadget/loop `Spec` is stated (proofs may be `sorry` **only** in this
  scaffolding commit, tracked in a checklist at the top of `Gadgets.lean`).
**Pitfalls:** `foldlRange` needs `ConstantLength`; branching on parity must not
change op count. Constants passed as `.const` expressions keep `muxConst4` at 1 alloc + 1 row.
`assertLtOrder` builds its runs from `boundRuns`; keep that function (M4 uses it).

### T0.3 Literal constant tables (S)

**Goal:** replace `fixedTables`/`fixedShift` (computed by 256-bit `bsmul` + inversion,
reduced mod n) with literal `Fp` values so proofs never evaluate `mulG`.
**Deliver:** `scripts/gen_projected_constants.py` (pure Python, reuse
`scripts/p256_reference.py`) emitting `Solution/Projected/Constants.lean`:
`tableX tableY : Fin 128 → Fin 4 → Fp` (as `#[...]` literals + `getD`), `shiftX shiftY`.
**Accept:** an executable test (`#eval` or in `Check.lean`) that the literals equal
`Offset.fixedTables`/`fixedShift`; T0.2's circuit uses the literals.
**Note:** the code's `mulG` reduces scalars mod n; certificates (M2) instead prove
`T_{i,d} = ((4+d)·4^i)•G` and `S = (4·(4^128−1)/3)•G` with **unreduced** scalars, which
needs no knowledge of `ord(G)`.

### M1 Group-form spec (M)

**Read:** `Projected/NaturalBoundLF.lean`, `RepresentationIndependent.lean`,
`P256Bridge.lean`, `ECBridge.lean` (`toMathlibPoint_bsmul`, `toMathlibPoint_add`,
`toMathlibPoint_infinity`, `toMathlibPoint_eq_iff_ProjectiveEquiv`).
**Deliver** `Solution/Projected/Math/GroupSpec.lean`:
```lean
def GroupSpec (pkX pkY digest r s : K) : Prop :=
  ∃ (E t : ℕ) (ry : K) (hQ : OnCurve pkX pkY) (hR : OnCurve r ry),
    E < 2^256 ∧ (E : K) = digest ∧ r.val < n ∧ t < n ∧ n - t = s.val ∧
    r ≠ 0 ∧ (t : K) ≠ 0 ∧ pkX ≠ 0 ∧
    G + pt pkX pkY hQ ≠ 0 ∧ pt r ry hR + G ≠ 0 ∧ pt r ry hR + pt pkX pkY hQ ≠ 0 ∧
    G + (pt r ry hR + pt pkX pkY hQ) ≠ 0 ∧
    E • G + r.val • pt pkX pkY hQ + t • pt r ry hR = 0
theorem spec_iff_groupSpec : Spec pkX pkY digest r s ↔ GroupSpec pkX pkY digest r s
```
(`OnCurve x y := y^2 = x^3 + a*x + b`.) Route: `Spec` = `BoundLF … r.val s.val`
→ `p256_boundLF_iff_representation_independent` → translate
`OriginalFiniteSums` (Z ≠ 0 of Longfellow `addE`) to `≠ 0` in `W.Point` via
`addE_nonzero`/`toMathlib_eq_zero_iff`, and `ScalarCombination .X = 0 ∧ .Z = 0` to the
group equation via `toMathlibPoint_bsmul` and `bsmul`/`natToBits` round trip
(`natFromBits (padBits (natToBits k) 256) = k` for `k < 2^256`).
**Accept:** theorem proved, axioms clean. If an exclusion form is awkward, an
equivalent phrasing is fine but must be stated purely over `W.Point`.

### M2 P-256 constant certificates (L) — math risk #1

**Goal (Lean statements):**
```lean
theorem table_pt (i : Fin 128) (d : Fin 4) :
  ∃ h, pt (tableX i d) (tableY i d) h = ((4 + d.val) * 4^i.val) • G
theorem shift_pt : ∃ h, pt shiftX shiftY h = (4 * ((4^128 - 1) / 3)) • G
theorem small_multiples_ne_zero : ∀ m, 0 < m → m < 4 * N_H → m • G ≠ 0
```
with `N_H` the offset-candidate count fixed by M3 (≥ catalogue size + 1, ≈ 1,040,
so `m < 4,160`; choose a round bound like 4,200).
**Method:** a Python generator emits chains of affine steps with slopes:
`B_0 = G`, `B_{i+1} = 4·B_i` (two doublings), `T_{i,d} = 4B_i + d·B_i` (≤ 3 adds),
`S = Σ 4·B_i` (prefix sums), and `k·G` for `k = 1..4N_H`. Each step is checked in
Lean by a lemma of the form "the three slope/x/y equations hold mod p and the
denominator is nonzero" stated over `Nat` literals and proved by `decide`; then
`AffineBridge.affine_add_eq_group` / `affine_double_eq_group` turn each step into a
group equation, and an induction over the chain gives the scalar statements.
Point validity (`OnCurve`) of each chain point comes from `Algebra.affine_add_onCurve`.
Split generated files to keep each under ~500 checks; record total build time.
**Accept:** the three theorems, axioms clean, build time reported (target < 15 min total).
**Implementation notes (M2a, in progress):** the generator `scripts/gen_projected_certs.py`
emits 13 chunk files `Certs0..12` (chained imports, ~5000 affine-step blocks) plus a
chained tail `CertsT0..` holding the 512 `tab`/`tab_pt` lemmas, `table_pt_aux`,
`shift_pt_aux`, and the 4200 `kG_ne` lemmas + `small_multiples_ne_zero_aux`.
Generated headers carry `set_option maxRecDepth 1000000` and
`set_option maxHeartbeats 8000000`.
**Original CertsT0 / fin_cases plan (historical; use the [M2 handoff](./m2-progress-report.md#next-assignment) for the next task):**
1. Lower `TAIL_CHUNK` (700 → ~128) so the 512 tab lemmas spread over several
   `CertsT*` files and compile in parallel instead of serializing in one file.
2. Prove `tab_{i}_{d}` with `by constructor <;> rfl` instead of `by decide` — same
   kernel reduction of `tableXList.getD`, but skips `Decidable`-instance elaboration
   (the observed heartbeat timeouts were in `whnf`/`isDefEq` during elaboration).
3. Fallback if a single lemma still times out: state tab lemmas at Nat level
   (`(tableX i d).val = (cT.._x).val ∧ ... := by decide`) and lift via
   `ZMod.val_injective` in `tab_pt`.
4. Keep `table_pt_aux` as `fin_cases i <;> fin_cases d <;> exact tab_pt_{i}_{d}`
   (`exact` = defeq; `rw` fails because `fin_cases` produces `⟨i, ⋯⟩` literals that
   don't syntactically match `OfNat` literals).
5. Give the `fin_cases fm` over `Fin 4200` in `small_multiples_ne_zero_aux` its own
   tail file so it cannot block the other tail files.
6. Verify incrementally: build one tail file at a time and record per-file time
   before running the full build.
**Pitfalls:** never unfold `ZMod` arithmetic on 256-bit literals inside `decide`;
prove a bridge lemma `(a : K) * b = c ↔ (a.val * b.val) % p = c.val` once and feed
`Nat` facts. Coordinates of `k•G` for small `k` are only needed to show `≠ 0`.

### M4 Comparator semantics (M)

**Read:** `Optimized.assertLtOrder`, `boundRuns`, `OptimizationLemmas.lean`.
**Deliver** `Math/Comparator.lean`:
```lean
theorem ltOrder_iff (b : Fin 256 → K) (hb : ∀ k, b k = 0 ∨ b k = 1) :
  (∀ run ∈ zeroRuns, ∃ q, missing run b * q = sum run b) ↔
  (∑ k, (b k).val * 2^k) ≤ n - 1
```
plus the completeness form (honest `q = sum * missing⁻¹` works). Steps: (1) `boundRuns`
evaluates to a concrete 68-run list (`decide`/`rfl`); (2) field sums of ≤ 256 booleans
are `0` iff all zero (cast of Nat ≤ 256 < p); (3) reduce to `gatedBits_correct` and
`lexLE` ↔ numeric `≤` on MSB-first bit lists. Missing-count semantics: per
`Optimized.assertLtOrder` docstring.
**Accept:** theorem + completeness lemma; statement phrased so G9 can use it with
the gadget's run-by-run constraint list.

### M5 Bit recomposition (S)

**Deliver** `Math/Bits.lean`: for boolean `b : Fin 256 → K`,
`(∑ k, b k * 2^k : K) = ((∑ k, (b k).val * 2^k : ℕ) : K)`, Nat sum `< 2^256`;
if Nat sum `< n` then `.val` of the field sum equals it; existence of a boolean
decomposition for every `N < 2^256` (completeness); digest lift: any `E < 2^256`
with `(E:K) = digest` is realisable.

### M6 Ladder and fixed-base group algebra (M)

Pure `AddCommGroup` lemmas (no curve), `Math/Ladder.lean`:
* **Fixed-base telescope:** `T_i = (4 + d_i)·4^i • G`, `S = Σ_{i<128} 4·4^i • G`,
  `ep_0 = H − S`, `ep_{i+1} = ep_i + T_i` ⇒ `ep_128 = H + (Σ d_i 4^i) • G`, and
  `Σ d_i 4^i = Σ e_k 2^k` when `d_i = e_{2i} + 2e_{2i+1}`.
* **Alternating ladder:** `acc_0 = −H`, `acc_{j+1} = 2•acc_j + X_j + σ_j•3H`
  with `σ_j = +1` (j even), `−1` (j odd) ⇒
  `acc_j = C_j − H` for even `j`, `C_j + H` for odd `j`, where `C_0 = 0`, `C_{j+1} = 2C_j + X_j`
  (use `OffsetExistence.elm_offset_step_invariant`). Hence `acc_256 = C_256 − H`.
* **Horner:** `X_j = r_{255−j}•Q + t_{255−j}•R` ⇒ `C_256 = r•Q + t•R`.
* Final: `−ep_128 = acc_256` ⟺ `E•G + r•Q + t•R = 0`.
* Partial-sum closed forms `ep_i = H − S + P_i`, `acc_j = C_j ± H` exported for M3.

### M7 Longfellow table lowering (M)

**Read:** `Baseline/Circuit.lean` (`addE`, `pointEquality`, `mat`, `assertZeroLazy`),
`vendor/longfellow/ECDSA/EcdsaCircuit.lean` (`ValidPreComputationExact`, `IsPointEquality`),
`EC.lean` (`addE`).
**Deliver** `Math/LongfellowTable.lean`: evaluation lemma — under an environment
satisfying the rows emitted by the lowering, the returned `(X3,Y3,Z3)` evaluate to
`(_root_.addE P Q params).X/Y/Z`; `pointEquality` rows ↔ `IsPointEquality`. Coordinate
with T0.2: either prove for the generic `mat`-based lowering or for the explicit
`mulWire` re-expression T0.2 produces (preferred: prove the explicit one, since the
gadget is now a fixed sequence of 6 `mulWire` + pending products).
Also: `ValidPreComputationExact`-shaped group statements (`pt pre₄ pre₅ = R + Q`, etc.)
via `toMathlibPoint_eq_iff_ProjectiveEquiv`, consumed by C3.

---

## 7. Wave 1 — gadget proofs (all parallel after T0.2)

Each G-task: prove `soundness` and `completeness` of the gadget exactly as frozen in
T0.2, plus its local `CostIs`, `IsR1CSCirc`, `UsesIRCirc` lemmas (cost numbers in §1.1).
Use `circuit_norm` and Clean's subcircuit lemmas; gadgets are small (≤ 6 rows) so
unfolding them is fine.

| ID | Gadget | Math used | Size |
|---|---|---|---|
| G1 | `nonzero`, `mulWire` | `mul_inv_cancel₀` | S |
| G2 | `bit3` / `assertBool` | `b*b=b ↔ b=0∨b=1` | S |
| G3 | `isOnCurve` | ring | S |
| G4 | `affAdd`, `affDouble` | `affine_add_eq_group`, `affine_double_eq_group`, `affine_add_onCurve`, `affine_double_onCurve`, `double_denominator_ne`, `P256Algebra.*` | M |
| G5 | `elm`, `elmTo` | `elm_eq_group`, `elm_output_onCurve`, `elm_second_denominator_ne` | M |
| G6 | `mux4`, `muxConst4` | case split on booleans; `muxConst4` coefficients `v0 + (v1−v0)b0 + (v2−v0)b1 + (v3−v2−v1+v0)b0b1` | S |
| G7 | `originalTable` | M7 | M |
| G8 | bit recomposition rows (3 `assertZero`) | M5 | S |
| G9 | `ltOrder` | M4 | M |

Completeness notes (for C5): `affAdd` needs `Q.x ≠ P.x`; `elm` needs `T.x ≠ A.x`
and `2A + T ≠ O` (so `A.x ≠ U.x`); `elmTo` additionally needs the target to equal
`2A+T`; `affDouble` needs only on-curve (2-torsion-free: `CurveHasNoPointsOfOrder2`).
`ltOrder`: honest quotient `sum · missing⁻¹` (with `0⁻¹ = 0`) works iff bound holds.

**Cost/R1CS/IR utilities (G0, S, do first in Wave 1):** `CostR1CS.lean` has
`CostIs.subcircuit`/`assertion` but no `subcircuitWithAssertion` variant; add
`CostIs.subcircuitWithAssertion`, `IsR1CSCirc.subcircuitWithAssertion` (copy the
existing proofs) in `Solution/Projected/Proof/Util.lean`. Do not edit the trusted util.

### M3 Offset existence on P-256 (L) — math risk #2 (after T0.2 catalogue, M2, M6)

**Deliver** `Math/OffsetGood.lean`:
```lean
def Good (inp) (E t ry) (c : ℕ) : Prop := ∀ k : Fin m, coeff k • (c • G) ≠ target inp E t ry k
theorem exists_good (h : GroupSpec-data) : ∃ c, 1 ≤ c ∧ c ≤ N_H ∧ Good … c
theorem good_implies_nonexceptional : Good … c → <every condition of the catalogue, phrased
  on the actual intermediate points (ep_i, acc_j, T_j, 3H, …) with H = c•G>
```
`coeff k ∈ {±1,±2,±3,±4}`, `target k` built from `Q, R, E, r, t` and M6 partial sums.
Instantiate `exists_avoiding_injective_equations` with `C = Fin N_H` (`c ↦ c+1`);
injectivity of `c ↦ a•(c•G)` from `small_multiples_ne_zero` (M2) since
`a(c₁−c₂)•G = 0` with `0 < |a(c₁−c₂)| < 4N_H`. Also derive `H ≠ O` and `3H ≠ O`.
**Accept:** `exists_good` and `good_implies_nonexceptional` proved for the exact
catalogue; any discrepancy with the code reported back to T0.2's owner.

---

## 8. Wave 2–3 — composition

### C1 Fixed-base chain soundness + completeness (M) — after G4, G6, M2, M6
Loop invariant over `foldlRange 128`: state point `P_i` on curve and
`pt P_i = pt H − S + Σ_{k<i} T_{k,d_k}`; conclude `pt ep = pt H + E•G`.
Completeness: under catalogue conditions for this group, all `affAdd` preconditions hold
and the honest state equals the affine coordinates of the invariant point.

### C2 Ladder soundness + completeness (L) — after G5, G6, M6
Invariant over the 127 double steps + 2 peeled steps: `pt acc_j = C_j ∓ H` (M6).
Soundness end result: `pt target = C_256 − H` where `target = (ep.x, −ep.y)`.
Completeness: preconditions of every `elm` from `good_implies_nonexceptional`.
Also the offset tables (group H): `pt plus_k = 3H + X_k`, `pt minus_k = −3H + X_k`.

### C3 Top-level soundness (M) — after C1, C2, G1–G9, M1, M4, M5, M7
```lean
theorem soundness : GeneralFormalCircuit.Soundness K main Assumptions Spec
```
Chain: constraints ⇒ (bits boolean, recompositions, comparators, curve/nonzero,
original table, `ep = H + E•G`, `−ep = rQ + tR − H`) ⇒ `GroupSpec` with
`E := Σe_k2^k`, `t := Σt_k2^k`, `r.val = Σr_k2^k` (M5 + comparator, `< n < p`),
`s.val = n − t` (from `Σt = n − s` in `K`, `0 < t < n`) ⇒ `Spec` via M1.
The four finite-sum exclusions come from the original table (M7 +
`pre_implies_finite_sums`).

### C5 Honest hint (M) — after M1, M3
`honestHint input`: from `Spec` (classical choice when it holds, defaults otherwise)
pick `(E, t, ry)` per `GroupSpec`, `pre` = affine coordinates of
`G+Q, R+G, R+Q, G+(R+Q)` (exist by exclusions), `c := Nat.find (exists_good …)`,
`H = c•G` as affine coordinates, bits of `E, r.val, t`. Encode rows exactly per §1.1
(`ProverHint` returns `#[]` for other keys/sizes). Lemmas: each row decodes to the
intended value.
Optional but recommended: a computable twin used by `Check.lean` (search `c = 1..N_H`)
and an executable test that it agrees with the vectors' satisfying H.

### C4 Top-level completeness (L) — after C1, C2, C5, G*
```lean
theorem completeness : GeneralFormalCircuit.Completeness K main ProverAssumptions ProverSpec
```
Using `UsesLocalWitnessesCompleteness`, show each subcircuit's completeness
assumption from the honest values and `Good` (M3). Final `elmTo` target equality is
exactly the group equation of `GroupSpec`.

---

## 9. Structural obligations (Wave 1–2, parallel with proofs)

| ID | Obligation | Approach | Size |
|---|---|---|---|
| O1 | `mainCost : circuitCost main ⟨4631, 4636⟩` | `CostIs.bind/foldlRange/mapFinRange/subcircuit*` + per-gadget counts; arithmetic by `norm_num` | M |
| O2 | `isR1CS main` | `IsR1CSCirc.*` per gadget; affine-input lemmas (`AffineProvable`, `affine_varFromOffset`); inputs to `mux`/`affAdd` are affine expressions | M |
| O3 | `witgenIsIR main` | `UsesIRCirc.*`; all witnesses are `witnessField` FExpr (`hintGet`, `mul`, `inv`, `add`) | S |
| O4 | `computableWitness` | witness exprs read only earlier locals and hints; follow Clean examples (`Clean/Gadgets/*`) | M |
| O5 | `requirementsChannelsLawful` | no channels: `elaborated.channelsWithGuarantees = []`; should be by `simp` | S |

Also `instance elaborated : ElaboratedCircuit K Input unit main` (from T0.2).

---

## 10. Wave 4 — F1 assembly and audit (M)

* `Solution/Projected/Submission.lean` fills every template slot; `Cost.lean` set to
  `4631`/`4636`.
* `scripts/check.sh`, `scripts/check_axioms.py` and `scripts/check_comparator.py`
  extended to the projected instance; axiom report committed
  (`Baseline/Projected/proof-validation.txt` style).
* End-to-end corollary (documentation value): `Spec ↔ BoundLF` is definitional, so a
  satisfying assignment implies the existence of a Longfellow witness binding `(r, s)`.
* Re-run vectors and matrix checker; update `Baseline/Projected/README.md`,
  `docs/ecdsa-optimization-handoff.md` "Still required" list, and §12 below.

---

## 11. Optional Track B — standard ECDSA (after Track A)

Only if the spec is broadened (D1 Track B). Estimates from the handoff (unmeasured):
B1 new trusted spec (standard P-256 verification, `r = R.x mod n`, no exclusions,
32-byte digest as two 128-bit limbs); B2 circuit: build shifted tables directly
(−74), drop `pkX ≠ 0` (−2), overflow bit + gated comparator for `R.x = r + n` (≈ +70),
digest limbs (+1) ⇒ ≈ 9,262; B3 re-prove D-, C-, F-dependent pieces (most gadgets,
M2–M6, C1–C2 reused; M3 catalogue changes); B4 spec bridge (new M1). Re-check the
233-point slack after B2's measured count.

---

## 12. Risk register and decision log

| Risk | Impact | Mitigation |
|---|---|---|
| Kernel time for M2 certificates (~5k affine steps) | build hours | Nat-level checks, split files, reduce `N_H` by tightening the catalogue |
| Catalogue miscount (M3 vs code) | completeness hole | T0.2 produces it from code; M3 cross-checks; executable test that `Good c` predicts `Check.searchH` |
| `foldlRange` proofs with large closure state slow | elaboration time | keep loop state = one `Point`; tables/bits passed as closed-over `Var`s |
| A redundancy argument fails (e.g. second ELM guard) | +512 score → over budget | already proved (`elm_second_denominator_ne`); do not weaken |
| Spec mismatch discovered in C3 | soundness fix costs points | slack 233; log any change here |
| `ProverHint` dependent-type encoding awkward | C5 delay | encode as `fun key k => if h : key = "offset" ∧ k = 1 then … else #[]` |

Decision log (append; one line per decision with date and score impact):

* 2026-11-17 — plan created; target Track A, score 9,267, slack 233.

---

## 13. Briefing template for subagents

```
You are working in <repo> on <assigned branch/worktree per §3>. Do not read other branches.
Read docs/ecdsa-proof-plan.md §1–§5, then task <ID> (§<n>).
Inputs you may rely on: <list of completed tasks + their files/theorem names>.
Work on one named lemma at a time; build the smallest target that checks it.
Keep frozen statements unchanged. If one appears false, stop and report the
counterexample or missing hypothesis; do not admit it.

Stop after two distinct approaches fail on the same goal, or after 20 minutes
without narrowing the failure, whichever comes first. Record the lemma, exact
goal/error, smallest reproducing command, attempts and next experiment.
Switch to an independent ready task if available. If a named consumer needs
the missing lemma, first prove its part with that lemma as an explicit hypothesis
in a helper, without changing the promised theorem. Only if that is impractical
may you use one labeled `sorry` at the missing lemma in an uncommitted draft.
Record its consumer; mark the lemma and dependent deliverables provisional.
Do not introduce a placeholder into a trusted spec or submit one as a proof.

Handoff each promised theorem as blocked, provisional, or verified. Verified
requires the intended statement, a green `lake build <module>`, and a recorded
`#print axioms <theorem>` containing only §3's allowed axioms. Report the build
time and next action; a build with `sorryAx` is not verification.
```
