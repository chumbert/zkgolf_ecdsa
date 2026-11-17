# Proof plan for the `circuit_baseline` ECDSA circuits

Status: planning document. No proofs are implemented yet.
This branch (`mistral-plan`) is created from `origin/circuit_baseline` (commit
`3a1bd20`) **only**. No other branch of this repository is fetched, merged, or
checked out; where older context is needed it is read via
`git show origin/circuit_baseline:<path>` or the refs already present locally.

**Plan B is the target**: prove the projected-signature circuit
  `Baseline.Projected.Offset.main`, measured score **9,267** (4,631 allocations
  + 4,636 R1CS rows) — under the 9,500 ceiling — against the
  representation-independent relation `RepresentationIndependentLF`
  (`[E]G + [r]Q + [n-s]R = infinity ∧ R.x = r`, retaining Longfellow's
  restrictions). Requires a new projected-signature challenge instance; the
  trusted pointwise instance stays untouched.

Toolchain: Lean `v4.34.0`; deps pinned by this branch's `lake-manifest.json`
(clean @ `93c9d1ef…`, mathlib @ `5ed29652…`). Axiom hygiene: every proved
theorem must depend only on `propext`, `Classical.choice`, `Quot.sound` — no
`sorryAx`, no `native_decide` (enforced via `scripts/check_axioms.py`).

---

# Plan B — prove `Baseline.Projected.Offset` at score 9,267 (≤ 9.5k)

## B0. Target, contract, and the critical gap

- **Circuit**: `Baseline.Projected.Offset.main` (`Baseline/Projected/Offset.lean`,
  188 lines). Interface `Input Fp` = 5 statement fields
  `(pkX, pkY, digest, r, s)`. Measured **9,267 = 4,631 + 4,636**
  (`Baseline/Projected/README.md`, `validation.txt`); `lake exe projected`
  shows 0 non-R1CS assertions and 252/252 native-vector agreement.
  The handoff's 9,261–9,262 estimate (`docs/ecdsa-optimization-handoff.md` §5)
  is only for the *optional* full-standard-ECDSA extension — out of scope; the
  cost goal is to **prove exact cost 9,267**, already under the 9.5k ceiling.
- **Relation**: `RepresentationIndependentLF pk digest r s n params`
  (`Baseline/Projected/NaturalBoundLF.lean`); the bridge
  `RepresentationBridge.P256.p256_boundLF_iff_representation_independent`
  (`Baseline/Projected/P256Bridge.lean`) already proves
  `BoundLF … ↔ RepresentationIndependentLF …` on the exact P-256 parameters,
  axiom-clean (`#print axioms` at the end of that file).
- **Critical gap found in `Offset.lean`**: all internal witnesses (`ry`,
  `H = (hx,hy)`, the 8 table coordinates, the 768 scalar bits) are allocated via
  `hint i = Circuit.witnessField (.hintGet "offset" …)` — prover-hint reads.
  `witgenIsIR` tolerates `.hintGet` (still `.ir` data), but **`computableWitness`
  forbids hint-reading generators**, and completeness is only provable against
  the circuit's own default generators. The hints must be replaced by
  input-computable IR witnesses before any proof can go through (Phase B2).

### Clean semantics relied on (clean @ 93c9d1ef)

- `GeneralFormalCircuit.Soundness` (`Clean/Circuit/Formal.lean:154`) concludes
  both `Spec …` **and** `Operations.Requirements env ops`
  (`Clean/Circuit/Operations.lean:820`) — the latter licenses reading each
  `witness e c` operation as "wire = `c.eval env`".
- `circuitCost`/`CostIs` (`Challenge/Utils/CostR1CS.lean:300-330`) ships
  compositional lemmas (`CostIs.bind`, `CostIs.witnessVector`,
  `operationCount_append`).
- `Challenge/Utils/WitgenIR.lean` provides `UsesIRCirc.*` combinators and
  documents that `computableWitness` rules out `.hintGet`/`.dataGet` reads.

## Phase B1 — Setup & new instance (2 tasks, sequential)

- **B1.1**: create the implementation work branch from `origin/circuit_baseline`
  only (worktree or `git switch -c` from that ref). Run
  `lake build projected Baseline.Projected.Audit`, `lake exe projected`,
  `python3 scripts/check_axioms.py`; record 4,631 / 4,636 / 9,267 / 0
  violations / 252-252. Add a `Proofs/` library to `lakefile.lean` with skeleton
  modules (`Proofs/Semantics.lean`, `Proofs/Gadgets.lean`, `Proofs/Loops.lean`,
  `Proofs/Assembly.lean`, `Proofs/Cost.lean`, `Proofs/Structure.lean`,
  `Proofs/Main.lean`) that compile.
- **B1.2**: new challenge instance
  `Challenge/Instances/ECDSA_P256_Projected/{Interface,Challenge,Cost}.lean`
  mirroring `ECDSA_P256_Digest`, but `Input` = the 5-field
  `Baseline.Projected.Offset.Input`, `Assumptions = True`,
  `Spec input () _ = RepresentationIndependentLF {pkX,pkY} digest r s n params`
  (mind the digest lift: the relation's `E` is an integer with the
  canonical/`digest+p` two-lift semantics already encoded in
  `BoundLF`/`RepresentationIndependentLF` — reuse, don't reinvent).
  Leave `ECDSA_P256_Digest` untouched.
  **Acceptance**: `lake build` green; `#print axioms` clean on the bridge.

## Phase B2 — Witness-computability refactor (critical path; checkpoint)

- **B2.1**: classify every `hint i` site in `Offset.lean` (`ry`, `hx`, `hy`,
  `pre[8]`, `be/br/bs[256]`): which are determined by inputs + earlier wires
  (bits of `E`, `r`, `n-s`; `pre` consistent with `addE`) and which need prover
  choice (`ry` square root, `H` exceptional-offset avoidance).
- **B2.2 (decision checkpoint)**: replace hint-reads with
  `witnessField`/`witnessIR` programs computing from the 5 inputs only.
  Recommended: bits via `.bit` FExprs of input-derived elements (canonical
  digest lift); `pre` via constrained wires tied to `addE` outputs; `ry` and
  `H` via unrolled IR search over a **proved-finite** safe candidate family
  (e.g. `H = kG` with `k` in a certified range from `OffsetExistence.lean`
  instantiated concretely like `P256Algebra.lean` does; `ry` fixed by the curve
  equation and the final group equation's sign). Fallback if IR computation of
  scalar-mult-mod-n is impractical: widen `Input` with `ry, hx, hy` (inputs are
  not scored, so 9,267 is preserved) and move their well-formedness into the
  spec — score-neutral but a contract change, so prefer the IR route.
  **Acceptance**: no `.hintGet`/`.dataGet` in any reachable witness op;
  `witgenIsIR` and `computableWitness` both provable.

## Phase B3 — Gadget semantics (parallel)

- **B3.1** (`Proofs/Semantics.lean`): lowering-semantics lemmas for
  `mat`/`assertZeroLazy`/`sel`/`assertBool`/`mm`/`pm` (`Baseline/Circuit.lean`,
  `Baseline/Optimized.lean`): affine-result invariant for `mat`;
  `assertZeroLazy e` + Requirements + constraints ⇒ `e.eval env = 0`;
  Requirements extraction helpers; bind / `for i in [0:256]` (constant-length
  loop) plumbing.
- **B3.2** (`Proofs/Gadgets.lean`): `affAdd`/`affDouble`/`elm`/`elmTo`
  (`Offset.lean:26-72`) soundness/completeness against the group law, using the
  already-proved `Algebra.lean` (ELM identities, redundant-denominator results),
  `AffineBridge.lean`, `ProjectiveBridge.lean` (affine/ELM rows produce the
  same group points as `addE`/`doubleE`), and `Ecdsa.lean`'s
  `ecdsaLoopResult_eq_tripleScalarMul_general`-style lemmas.
- **B3.3**: `mux4`/`muxConst4` selection correctness via `Optimized.sel`
  interpolation on boolean bits; `fixedTables`/`fixedShift` are constants.
- **B3.4**: `Optimized.assertLtOrder` soundness for `r < n` and `n-s < n` via
  `Baseline/OptimizationLemmas.lean`'s `quotient_gate` + `gatedBits_correct`
  (already proved) + bit-boolean facts from B3.3.
- **B3.5**: `originalTable` (retained Longfellow precomputation checks) via the
  circuit-`addE` vs `EC.lean`-`addE` coordinate equivalence (`ring`-level) and
  `pointEquality` ⇒ `IsPointEquality`.

## Phase B4 — Loop invariants (1 big task, splittable)

- **B4.1**: induction over the 128-window fixed-base ladder (`ep` accumulating
  `[E]G` with constant `fixedShift`) and over the 256-step joint ladder (`acc`,
  MSB-first, `mux4` over the `plus`/`minus` offset tables
  `H, 3H, 3H±Q, 3H±R, 3H±QR`), ending in `elmTo acc t (ep.1, -ep.2)` asserting
  `[E]G + [r]Q + [n-s]R = infinity`. Split: B4.1a one-step lemma; B4.1b
  256-fold induction; B4.1c final-step special case. Connect to
  `RepresentationIndependentLF` via `ProjectiveBridge` and
  `BoundLF.core_loop_group_iff` (`BoundLF.lean:84`). Kernel-performance guard:
  one-step lemma + `List.range` induction; never `decide` on the whole circuit.

## Phase B5 — Assembly (1 task)

- **B5.1**: prove the seven obligations for the new instance's `main`.
  Soundness: constraints ⇒ all conjuncts of `RepresentationIndependentLF`
  (on-curve pk/R/H; nonzero `pk.x`, `r`, `n-s`; comparator bounds; table
  checks; group equation; `R.x = r`; digest reconstruction with the two-lift
  semantics). Completeness: spec ⇒ the B2.2 default IR witnesses satisfy every
  assert (here the instantiated safe-`H` existence theorem from
  `OffsetExistence.lean` does the work).

## Phase B6 — Cost & structure (parallel)

- **B6.1** (`Proofs/Cost.lean`): `mainCost = ⟨4631, 4636⟩` via `CostIs.bind` and
  per-gadget counts (`affAdd`, `affDouble`, `elm`, `elmTo`, `nonzero`, `mux4`,
  `assertBool`, `assertLtOrder` = 34 zero-run quotient rows, `originalTable`),
  summed with `Count.add` simp lemmas + `omega`; cross-check against
  `lake exe projected --count-only`. No `native_decide`; no whole-circuit
  `decide`.
- **B6.2** (`Proofs/Structure.lean`): `isR1CS` — every assert from
  `mat`/`assertZeroLazy`/`sel` has ≤ 1 product of affine forms; `assertBool`
  (`b*b - b`) and the quotient row are single-product by construction.
- **B6.3**: `witgenIsIR` — after B2.2 all witnesses are `.ir`; structural via
  `UsesIRCirc.*`.
- **B6.4**: `computableWitness` — B2.2 generators read only inputs + earlier
  wires (program-order allocation ⇒ offset ordering).
- **B6.5**: `elaborated` + `requirementsChannelsLawful` (no lookups/interactions).

## Phase B7 — Audit & packaging (1 task)

- **B7.1** (`Proofs/Main.lean`): export the seven theorems with the exact types
  of the new instance's `Challenge.lean`; `#print axioms` each (only the three
  standard axioms); wire into `scripts/check_axioms.py`; keep
  `lake exe projected` (vectors + mutations) green; write `Proofs/README.md`
  mapping each obligation to the vendored lemmas it uses.

## Plan B dependency graph

```
B1.1 ─ B1.2 ─┬─ B2.1 ─ B2.2 (checkpoint) ─┬─ B3.1..B3.5 ─ B4.1 ─ B5.1 ─ B7.1
             └─ B6.1..B6.5 (B6.3/B6.4 need B2.2; rest independent of B4/B5) ─┘
```

Biggest risks: (1) B2.2 witness computability from 5 inputs — fallback widens
`Input` (score-neutral) at the price of a contract change; (2) B4.1 kernel cost
 of the 256-step induction.
