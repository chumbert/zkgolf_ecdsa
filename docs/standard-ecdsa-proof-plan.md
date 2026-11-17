# Standard P-256 ECDSA: proof and implementation plan

## 1. Target and evidence

**Target:** a fully proved R1CS verifier for standard P-256 ECDSA, using the
9,267-cost projected experiment as its implementation starting point. The proof
must bind the signature and exact 256-bit digest and cover every standard-valid
input, including exceptional inputs rejected by Longfellow's circuit.

This is an execution plan, not an implementation or a completed proof. It was
prepared on 2026-11-17 after inspecting:

| Source | Pinned revision | What it supplies |
|---|---|---|
| Local `optimized-proofs` | `4d57ece87d9968dc5cca653c97897beadfc08a9b` | Completed 18,612-cost pointwise circuit proof; reusable arithmetic, cost, audit and validation patterns |
| `compsec-epfl/zkgolf_ecdsa`, `circuit_baseline` | `3a1bd20749ae0b6400a158651dba64a2c5fc58ff` | Measured 9,267 experiment, ELM algebra/group bridges, abstract offset-existence proof |
| Longfellow proof sources | `4fe092be7e8e9634cd3b27daf55695a3a416043e` | EC arithmetic and compatible no-two-torsion certificate |

The planning branch is **`standard-ecdsa-proofs`**, based on the local
`optimized-proofs` revision above. Only this plan was added during planning.

The 9,267 experiment itself has no end-to-end circuit correctness theorem. Its
existing theorem `p256_boundLF_iff_representation_independent` is about an
existential projection of Longfellow acceptance. The target here needs a new
standard-ECDSA specification and a new equivalence theorem.

### Definition of done

1. A precise standard-ECDSA specification, independent of circuit internals.
2. Soundness for **every** satisfying assignment of all auxiliary wires.
3. Completeness for **every** standard-valid input, including an explicit proof
   that suitable offset and prover hints exist.
4. Correctness of the executable honest witness generator under those hints.
5. Exact allocation/row count and single-row R1CS certificates.
6. Witness-IR, fixed-hint causality and channel-lawfulness certificates.
7. Kernel-checked P-256 arithmetic facts used by correctness, with no remaining
   subgroup, candidate-injectivity or curve-order hypotheses.
8. An axiom audit allowing only `propext`, `Classical.choice`, `Quot.sound`.
9. Standard-ECDSA regressions, matrix checks, and a contract-specific verifier.

**Cost objective:** preserve the experiment's approximate size and aim for
**9,262 = 4,628 allocations + 4,634 rows**, as derived below. This is a proposed
budget, not a measured or proved result. Exact cost is a release gate.

## 2. Freeze the semantic contract first

### External circuit interface

Use six base-field inputs, in a fixed documented order:

```text
(pkX, pkY, digestLo, digestHi, r, s) : F_p^6
```

The circuit proves that each digest limb is below `2^128` by binding it to 128
Boolean digest bits. Define `E = val(digestLo) + 2^128 * val(digestHi)`.
The scalar inputs denote their canonical field representatives. The circuit
enforces `1 <= r < n` and `1 <= s < n`. The output is unit: satisfying the
constraints means verification succeeds.

This is a prehashed 256-bit-digest component. For SHA-256 ECDSA, `E` is the
big-endian integer represented by the supplied 32-byte digest. Byte adapters
must document endian conversion and reject noncanonical coordinate/scalar
encodings. Hashing a message is an enclosing component.

Whether these six values are public or private in an enclosing ZK application
does not change this arithmetic relation or the allocation accounting.

### Mathematical verification predicate

On the P-256 group, with identity `O` and generator `G`:

1. `Q = (pkX, pkY)` is an affine on-curve point, hence is not `O`.
2. `0 < r < n` and `0 < s < n`.
3. Let `w = s^(-1) mod n`, `u1 = E*w mod n`, `u2 = r*w mod n`.
4. Let `V = [u1]G + [u2]Q`.
5. Require `V != O` and `val(x(V)) mod n = r`.

Both high-s and low-s signatures are accepted. In particular, the predicate has
no original-table finiteness restrictions and no requirement `pkX != 0`.

Do not use the vendored `StandardEcdsaVerify` unchanged: in
`vendor/longfellow/ECDSA/EcdsaSpec.lean:52-55` its final condition is direct field
x-coordinate equality, despite its name/comment.

### Representation used by the smaller circuit

Prove the standard predicate equivalent to existence of an affine point `R`
such that, for `t = n-s`:

```text
[E]G + [r]Q + [t]R = O
val(R.x) mod n = r
```

Here `R` is finite and on curve, and `1 <= t < n`. Its x-coordinate need not
equal `r`: because `n < p < 2*n`, it is either `r` or `r+n`.

This equivalence requires certified group-order facts. A theorem conditional
on `[n]Q=O` or `[n]R=O` is useful internally but is not the final result.

## 3. Circuit changes and proposed cost

### A. Build only the shifted tables

Delete the *new standard circuit's* dependence on `originalTable`. For each
sign `epsilon` in `{+1,-1}`, construct:

```text
P0 = [3*epsilon]H
P1 = P0 + Q
P2 = P0 + R
P3 = P1 + R
table_epsilon = [P0, P1, P2, P3]
```

This uses six ordinary affine additions, as in the existing shifted-table
phase. It never asks for affine coordinates of unshifted `Q+R`. It therefore
works when `Q+R=O` or `Q=R`, provided the chosen offset avoids the actual
addition denominators. Table order must match `rBit + 2*tBit`.

### B. Support the x-coordinate reduction branch

Allocate one Boolean `overflow` and use the affine expression
`rx = r + n*overflow` as `R.x`. Keep the existing nonzero check on **r**, not
on a differently interpreted scalar.

Require `overflow=1 -> r < p-n`. This makes `r+n` an integer below `p`, so
field addition cannot silently wrap. Then prove:

```text
val(rx) = val(r) + n*overflowNat
val(rx) mod n = val(r)
```

A low-cost conditional comparator can use the zero-run construction already
proved for the original circuit. For each zero run of `(p-n)-1`, assert:

```text
(missingOnes + (1-overflow)) * quotient = runSum
```

When `overflow=1`, this is the usual bounded comparison. When `overflow=0`,
the first factor is a positive integer at most 257, so a quotient exists for
every Boolean r-bit vector. It remains one product per row. Multiplying an
existing quadratic assertion by `overflow` would instead make it cubic.

Both `n-1` and `p-n-1`, written as 256-bit integers, have 34 maximal zero runs.
This count was checked numerically during planning; it still needs a Lean
certificate for the actual run lists and their coverage.

### C. Bind the full digest

Replace the single digest recomposition with:

```text
sum_{i=0..127} 2^i * eBit[i]       = digestLo
sum_{i=0..127} 2^i * eBit[128+i]   = digestHi
```

These use the existing 256 digest bits and add one net assertion. Each sum
is below `2^128 < p`; prove integer equality from field equality. Unlike the
experiment's one-field digest, this binds `E` uniquely.

### D. Retain necessary scalar checks

Keep Boolean r/t bits, `rBits < n`, `tBits < n`, and nonzero r/t. Recompose
`tBits` to the field expression `n-s`, then prove the natural identity
`val(s)=n-t` using `0<t<n<p`. Do not replace that argument with unchecked
field subtraction. Remove the `pkX` inverse requirement.

### Budget ledger

| Modification from experiment | Allocations | Rows | Score delta |
|---|---:|---:|---:|
| Existing measured experiment | 4,631 | 4,636 | 9,267 |
| Remove original table hints/checks | -37 | -37 | -74 |
| Remove public-key x inverse check | -1 | -1 | -2 |
| Add overflow Boolean | +1 | +1 | +2 |
| Add 34 guarded bound rows/quotients | +34 | +34 | +68 |
| Split digest binding into two rows | 0 | +1 | +1 |
| **Proposed standard circuit** | **4,628** | **4,634** | **9,262** |

Independent proposed phase totals, useful for detecting accidental allocations:

| Phase | Allocations | Rows |
|---|---:|---:|
| Seed hints: ry, Hx, Hy, overflow, 768 scalar bits | 772 | 0 |
| On-curve Q, R, H | 6 | 9 |
| Nonzero r and t | 2 | 2 |
| Boolean scalar bits and overflow | 0 | 769 |
| Two digest and two scalar bindings | 0 | 4 |
| Three 34-run comparators | 102 | 102 |
| Fixed-base initial addition + 128 mux/add windows | 644 | 644 |
| Compute 2H and 3H | 8 | 8 |
| Six shifted-table additions | 24 | 24 |
| 255 mux/ELM steps + final mux/ELM-to-target | 3,070 | 3,072 |
| **Total** | **4,628** | **4,634** |

These totals assume the source's row geometries survive the port: `affAdd`
4/4, `affDouble` 4/4, `elm` 6/6, `elmTo` 4/6, variable mux 6/6,
constant mux 1/1. Count all seed hints as allocations. Only the six external
inputs are excluded. Bundled subcircuits must be costed after flattening.

## 4. Proof architecture and shared interfaces

### New modules

Use the root library/namespace `StandardECDSA`, separate from the existing
challenge-specific namespace. Suggested ownership boundaries:

```text
StandardECDSA/
  Interface.lean             -- six inputs; semantic and prover contracts
  Spec.lean                  -- standard verification predicate
  Math/
    P256.lean                -- field/curve facts and group representation
    GroupOrder.lean          -- prime n, order G, all-point n-torsion
    SignatureEquation.lean   -- standard verification iff three-term equation
    ScalarEncoding.lean      -- bits, naturals, canonical field values
    ConstantBounds.lean      -- zero runs and gated comparison
    FixedTables.lean         -- 512 entries, shift and scalar semantics
    OffsetConditions.lean    -- finite bad-equation family
    OffsetCandidates.lean    -- 1040 candidates and safe-offset existence
  Gadgets/
    Field.lean               -- multiplication, nonzero, curve assertion
    Scalar.lean              -- bits, limbs, r/t and overflow checks
    Affine.lean              -- guarded addition and doubling
    ELM.lean                 -- ELM and ELM-to-target
    Select.lean              -- variable and constant point muxes
  Phases/
    FixedBase.lean           -- ep = H + [E]G
    ShiftedTables.lean       -- tables of ±3H plus Q/R
    JointLadder.lean         -- alternating-offset scalar invariant
  Witness/
    Seed.lean                -- typed hint layout and admissibility
    Generate.lean            -- executable generation and bounded H search
    Correctness.lean         -- generation succeeds on every valid input
  Main.lean                 -- circuit assembly and correctness theorems
  Cost.lean
  R1CS.lean
  WitnessIR.lean
  HintCausality.lean
  Export.lean
Tests/StandardECDSA/
  Main.lean
  Axioms.lean
```

### Clean proof boundaries

Follow the supplied Clean `AGENTS.md` guidance:

* Bundle independently proved gadgets/phases as `FormalCircuit`,
  `FormalAssertion` or a suitable `GeneralFormalCircuit`/`WithHint`.
* Parents invoke the bundled subcircuit interface, not `Child.main`.
* Specs describe group/scalar semantics, not a renamed list of row equations.
* Begin soundness/completeness from the actual theorem and
  `circuit_proof_start`; add genuine mathematical lemmas where needed.
* Use explicit elaborated metadata where inference needs help. Use induction
  over typed loops, not unfolding hundreds of operations.
* Do not change `maxHeartbeats`. Diagnose proof structure/performance first.
* This environment has no Lean-MCP tools exposed. Use targeted `lake build`
  checks as the available fallback, and record module-level timings.

Freeze shared semantic types before parallel proof work:

1. One concrete Mathlib P-256 group type, with consistent affine lifting and
   projective transport lemmas.
2. A typed 256-bit vector, little-endian for arithmetic; the ladder explicitly
   consumes indices `255-j`.
3. `ScalarFacts`: E, r, t, s natural identities and all bounds.
4. `Seed`: 772 fields with named components and a versioned hint encoding.
5. `GoodOffset(Q,R,E,r,t,H)`: geometric admissibility of the actual affine
   operations, defined from group points, not from constraint satisfaction.
6. Phase specs giving group identities and finite/on-curve outputs.

An incomplete affine gadget's semantic spec should include both its group
result and its required distinct-x condition. Completeness assumes that
condition; the global offset theorem supplies it. Soundness derives it from
the enforced inverse row. This prevents preconditions from being mistaken for
unchecked caller assumptions.

### Correctness with hints: explicit change of verification contract

`Offset.hint` uses `FExpr.hintGet`. Under the currently pinned Clean definitions,
`ProverEnvironment.AgreesBelow` compares only wires, not hint providers.
Consequently the experiment cannot satisfy the old hint-independent
`Circuit.ComputableWitnesses` obligation. See
`Challenge/Utils/WitgenIR.lean:47-55` and Clean `Circuit/Basic.lean:424-438`.

For the new standard instance, prove all of the following:

1. **Unconditional witness soundness:** any environment satisfying the rows
   implies standard verification. There is no good-hint assumption here.
2. **Admissible-hint completeness:** actual local witness generation satisfies
   the rows for a valid input with its associated admissible seed/offset.
3. **Hint existence:** every standard-valid input has such an admissible seed.
4. **Executable generation correctness:** the bounded algorithm returns one
   on every standard-valid input.
5. **Fixed-hint causality:** generator evaluation agrees between environments
   agreeing on earlier wires and the relevant hint provider. External data
   reads must be absent or explicitly accounted for.
6. **Existential acceptance equivalence:** standard verification iff there
   exists an auxiliary assignment satisfying the actual circuit constraints.

Item 2 alone is not global completeness: otherwise `GoodOffset` could conceal
an unproved existence assumption. Item 5 must have a distinct, truthful name;
it is not the old `computableWitness` theorem. Keep all hint cells in the cost.

## 5. Critical mathematical arguments

### P-256 order certification without assuming a Hasse theorem is available

The existing P-256 bridge certifies nonsingularity and no rational two-torsion,
but not the group order needed here. A promising concrete proof route is:

1. Certify primality of n with a kernel-checked certificate.
2. Certify `G != O`, G on curve and `[n]G=O`; conclude `addOrderOf G=n`.
3. Conclude `n` divides the finite P-256 group cardinality N.
4. Bound `N <= 2*p+1`: at most two y-values for each affine x plus infinity.
5. Use the no-two-torsion certificate to prove N odd (for example, pair each
   nonidentity point with its distinct inverse).
6. Check numerically in Lean that `2*p+1 < 3*n`. Since N is a positive odd
   multiple of the odd prime n below `3*n`, conclude `N=n`.
7. Deduce `[n]P=O` for every group point P and injectivity of multiplication
   by 1, 2, 3 and 4 (and their negatives).

The arithmetic inequalities were checked during planning. The finite-field
root-count bound, finite-group argument and scalar-multiplication certificate
are still proof tasks. This route avoids treating a missing library Hasse
bound as an implicit dependency.

### Loop invariants

Fixed base, with `S = [4 * sum_{i<128}4^i]G` and window digit
`d_i=eBit[2*i]+2*eBit[2*i+1]`:

```text
ep_k = H - S + sum_{i<k} [(4+d_i)*4^i]G
ep_128 = H + [E]G
```

Joint ladder, before iteration j:

```text
C_0 = O
C_(j+1) = [2]C_j + T_j
T_j = [rBit[255-j]]Q + [tBit[255-j]]R
sigma_j = -1 when j is even, +1 when j is odd
acc_j = C_j + [sigma_j]H
selected_j = T_j - [3*sigma_j]H
acc_(j+1) = C_(j+1) - [sigma_j]H
```

Thus after 256 steps the represented point is `[r]Q+[t]R-H`.
`elmTo` constrains the last output directly to `-ep`, giving exactly
`[E]G+[r]Q+[t]R=O` after cancelling H.

Carry on-curve/finite facts through the invariant. The ELM soundness bridge
can reuse the proved redundant-second-denominator theorem; honest witness
construction must establish denominator nonzeroness independently before
using an inverse. Assuming the third ELM equation in order to construct the
inverse that makes that equation true would be circular.

### Concrete 1,039-exception budget for the revised tables

Let candidates be `H_k=[k]G`, `1 <= k <= 1040`. For a fixed valid signature
and fixed scalar bits, every bad condition below is an equation
`[a]H=B`, where `a` is one of `±1, ±2, ±3, ±4` and B is independent of H.

| Source | Number of equations |
|---|---:|
| H=O | 1 |
| Initial fixed-base `H + (-S)` and 128 window additions: same/opposite points | 2*129 = 258 |
| Six shifted-table additions: same/opposite points | 2*6 = 12 |
| 256 ELM steps: two first-addition collisions and one output-infinity collision | 3*256 = 768 |
| **Total** | **1,039** |

Details to formalize:

* For fixed-base input `H+P_i` and constant window `U_i`, forbid
  `H=U_i-P_i` and `H=-U_i-P_i`. The initial addition forbids `H=±S`.
* For each table sign epsilon, forbid
  `[3*epsilon]H=±Q`, `=±R`, and `=±R-Q`.
* At ELM step j, forbid
  `[4*sigma_j]H=T_j-C_j`,
  `[2*sigma_j]H=C_j+T_j`, and
  `[sigma_j]H=[2]C_j+T_j`.
* The other second-addition collision is `selected_j=O`; table construction
  already excludes it. Prove this implication explicitly.
* Doubling H is safe because there is no nonzero two-torsion. Adding 2H to H
  is safe because H is nonzero and the group has no nonzero three-torsion.
* Prove that equality of affine x-coordinates means points are equal or
  negatives, and that every required intermediate is finite.

Each equation excludes at most one candidate. Apply the source theorem
`RepresentationBridge.OffsetExistence.exists_avoiding_injective_equations`
after certifying the injection of each candidate map. This gives a usable
1040-candidate bound for the changed circuit if all the coverage obligations
above succeed. The count is not complete until every actual affine operation
is matched to a case in Lean.

## 6. Agent-sized task packets

Task IDs below are also proposed branch suffixes. Each task owns the listed
paths; integration/configuration changes go through the coordinator. Proposed
theorem names are interfaces to implement, not declarations already present.

### T00 — Pin sources and reproduce the experiment

**Owner:** integration agent. **Depends on:** none.

1. Record the two source revisions and verify clean worktree state.
2. Create a detached reference worktree at the experiment revision, e.g.
   `/tmp/opencode/zkgolf-circuit-baseline-3a1bd20`.
3. Reproduce `lake build projected Baseline.Projected.Audit`, the executable
   count and vector log, and exported-matrix checks there.
4. Import only needed mathematical modules into the working branch, recording
   provenance and any namespace/import adaptations. Review
   `Baseline/Projected/upstream-proof-provenance.json`.
5. Resolve the collision between the two branches' `Baseline/Check.lean`
   explicitly; do not overwrite it by importing the whole source branch.
6. Add the `StandardECDSA` library and a focused standard-test executable.

**Deliverables:** source manifest, reproducibility log, building library skeleton.
**Acceptance:** reference counter reports 4631/4636; imported proof roots pass
the permitted-axiom audit. Existing native interface remains independently
buildable on this branch.

### T01 — Standard specification and six-field interface

**Owner:** specification agent. **Depends on:** T00.
**Owns:** `Spec.lean`, `Interface.lean`.

1. Define exact digest limb decoding, canonical scalar decoding and the group
   verification predicate from Section 2.
2. Make nonzero-result and x-mod-n conditions explicit.
3. Specify rejection of out-of-range limbs/scalars as part of circuit validity.
4. Define a high-level alternate signature-point relation, initially with
   explicit group-order premises for its generic mathematical lemmas.
5. Freeze field order, endian convention, high-s acceptance and output type.
6. Specify a separate verifier contract for this instance; do not reuse the
   old comparator's pointwise theorem types.

**Acceptance:** specification compiles without any circuit imports; all later
tasks share its definitions rather than introducing competing predicates.

### T02 — P-256 group-order foundation

**Owner:** curve-foundation agent. **Depends on:** T00, group-type agreement T01.
**Owns:** `Math/P256.lean`, `Math/GroupOrder.lean`.

1. Port/reuse generator-on-curve, nonsingularity and no-two-torsion proofs.
2. Supply a kernel-checked n-primality certificate.
3. Build a tractable certified scalar-multiplication chain for `[n]G=O`.
4. Prove G has order n and the group cardinality is n, using the route in
   Section 5 or another fully checked route with stated dependencies.
5. Export `nsmul_order_eq_zero`, small-multiplier injectivity, finite/affine
   transport, and nonzero small generator multiples.

**Acceptance:** no residual order/cardinality assumptions; audit all exported
roots. Give timings for the concrete certificates. This is a critical-path
task and must start early.

### T03 — Standard verification iff signature-point equation

**Owner:** specification agent. **Depends on:** T01, T02.
**Owns:** `Math/SignatureEquation.lean`.

1. First prove the generic finite-group equivalence using n-torsion and
   invertibility of s modulo n.
2. Prove the inverse-based standard verification point is the same group point
   as an R satisfying `[s]R=[E]G+[r]Q`.
3. Rewrite `t=n-s` to obtain the three-term zero equation.
4. Prove the x-mod-n branch characterization using canonical x below p and
   `n<p<2*n`.
5. Specialize all premises to certified P-256 facts.

**Deliverables:** `standard_iff_signaturePoint`, `x_mod_order_iff_lift`.
**Acceptance:** both directions preserve exactly E, Q, r, s; no table or
Longfellow-validity predicate appears in the final statements.

### T04 — Hint semantics and executable seed interface

**Owner:** witness/framework agent. **Depends on:** T01.
**Owns:** `Witness/Seed.lean`, `HintCausality.lean`.

1. Define and document the typed 772-field seed layout.
2. Define admissibility via scalar facts, R and `GoodOffset`; agree that shared
   predicate's type with T13 before defining its mathematical body.
3. Define the hint provider and prove round-trip access for every seed index,
   including fixed row bounds and UInt64 conversion.
4. Define fixed-hint prefix agreement and prove structural witness-causality
   composition for the operations/subcircuits actually used.
5. State the global soundness, admissible-hint completeness, seed-existence and
   existential-acceptance theorem interfaces.
6. Establish a small hint-backed gadget example proving this contract fits
   the pinned Clean API before the rest of the port depends on it.

**Acceptance:** soundness cannot assume admissible hints; completeness does not
claim arbitrary hint providers are honest. No claim of old-style
`Circuit.ComputableWitnesses` for a `hintGet` leaf.

### T05 — Explicit field gadgets and circuit skeleton

**Owner:** circuit-foundation agent. **Depends on:** T00, T01, T04 interface.
**Owns:** `Gadgets/Field.lean`; initial assembly skeleton coordinated in `Main.lean`.

1. Port multiplication, Boolean assertion, nonzero and affine curve assertion
   into bundled proof boundaries with exact semantic specs.
2. Preserve the source's row shapes and use explicit operations whose counts
   do not depend on syntactic constant-folding branches in arbitrary inputs.
3. Prove local soundness/completeness, IR structure, output types and costs.
4. Ensure inverse witnesses are constrained; witness computation alone is not
   a nonzero assertion.
5. Freeze the numerical phase ledger and scaffold the six-input circuit.

**Acceptance:** building bundled leaves and per-leaf cost/R1CS certificates.
Parents can invoke them without traversing their operation lists.

### T06 — Pure scalar encoding and conditional comparison mathematics

**Owner:** scalar-mathematics agent. **Depends on:** T01.
**Owns:** `Math/ScalarEncoding.lean`, `Math/ConstantBounds.lean`.

1. Port applicable results from existing Soundness/Range and Completeness/Range
   and isolate a generic 256-bit constant-bound theorem.
2. Prove little-endian nat/field reconstruction and reverse-index identities.
3. Prove zero-run partition/coverage certificates for n-1 and p-n-1.
4. Prove soundness and quotient existence for the gated comparator, including
   all bounds preventing count sums from wrapping modulo p.
5. Prove canonical digest-limb binding, r binding, and `t=n-val(s)`.
6. Prove the overflow coordinate's canonical natural value, not merely its
   field equality.

**Acceptance:** proofs handle r=0,n-1,n; t=0,n-1,n; overflow=0/1;
r=p-n-1,p-n; maximal 128-bit limbs. The mathematical lemmas do not depend on
the new circuit's operation offsets.

### T07 — Scalar circuit proof

**Owner:** scalar-circuit agent. **Depends on:** T04, T05, T06.
**Owns:** `Gadgets/Scalar.lean`.

1. Allocate/retrieve the 768 bits and overflow once, with Boolean constraints.
2. Bind both digest limbs, r and n-s.
3. Instantiate two ordinary order comparisons and the guarded lift comparison.
4. Bundle the phase with a `ScalarFacts` spec.
5. Prove soundness from arbitrary assignments and completeness from matching
   seed bits and valid scalar data.
6. Certify its cost and R1CS form, including 34 quotient rows per comparator.

**Acceptance:** no unbounded integer-to-field inference; inactive overflow
branch remains complete. The final spec implies both signature scalars are
strictly between 0 and n.

### T08 — Affine addition and doubling circuit proofs

**Owner:** affine-gadget agent. **Depends on:** T02 curve interfaces, T05.
**Owns:** `Gadgets/Affine.lean`.

1. Port `affAdd` and `affDouble` with 4/4 costs each.
2. Apply the existing `Algebra` and `AffineBridge` theorems to the actual rows.
3. Include on-curve and group-operation semantics in bundled output specs.
4. For soundness, derive distinct x from the explicit guard, and derive
   doubling denominator nonzero from the slope row/nonsingularity.
5. For completeness, assume/prove actual denominator nonzeroness before using
   the generated slope inverses.
6. Prove negation transport and finite-coordinate equality as needed by parents.

**Acceptance:** no new doubling inverse row; counts 4/4 remain certified.

### T09 — ELM and direct-target circuit proofs

**Owner:** ELM-gadget agent. **Depends on:** T05, T08 shared group interfaces.
**Owns:** `Gadgets/ELM.lean`.

1. Port `elmCore`, `elm`, `elmTo`; bundle at meaningful semantic boundaries.
2. Connect actual row values to `elm_two_additions`,
   `elm_second_denominator_ne`, `elm_output_onCurve`, `elm_eq_group`.
3. Prove output group point `[2]P+Q`, plus needed admissibility facts.
4. Prove completeness using distinct-x hypotheses at both ordinary additions.
5. Treat `elmTo` as a semantic assertion against an already supplied target;
   do not allocate replacement output coordinates.

**Acceptance:** costs 6/6 and 4/6; no circular denominator proof; no additional
second-denominator guard or on-curve row.

### T10 — Multiplexer proofs

**Owner:** selector agent. **Depends on:** T05.
**Owns:** `Gadgets/Select.lean`.

1. Prove four-way variable selection with index `b0+2*b1` and cost 6/6.
2. Prove constant selection using one shared bit product, cost 1/1.
3. Use fixed-size tables so no unchecked `Array.getD` default participates in
   semantic correctness.
4. Export semantic selection equality and propagation of on-curve/finite facts.

**Acceptance:** all four Boolean choices proved; no separate bit-product
allocation for the second coordinate of the constant mux.

### T11 — Fixed generator table certification

**Owner:** constant-certification agent. **Depends on:** T02.
**Owns:** `Math/FixedTables.lean`.

1. Certify each of the 128*4 entries as `[(4+d)*4^i]G` and finite/on curve.
2. Certify the shift S and its affine coordinates, including S != O.
3. Prove scalar reduction modulo n is consistent with source `mulG`.
4. Prove the window sum and cancellation identity for every 256-bit E.
5. Choose computationally manageable per-window certificates/recurrences;
   seal certified constants behind semantic theorems.

**Acceptance:** every coordinate used by the circuit is covered by a kernel
proof. A generated table and sample on-curve checks are not sufficient.

### T12 — Fixed-base and shifted-table phase proofs

**Owners:** two agents may split by file. **Depends on:** T08, T10, T11;
T07 scalar interface and T13 admissibility interface.
**Owns:** `Phases/FixedBase.lean`, `Phases/ShiftedTables.lean`.

1. Fixed-base agent proves the Section 5 prefix invariant by 128-step induction.
2. Return the semantic result `ep=H+[E]G` and finite/on-curve facts.
3. Table agent constructs P1/P2/P3 in the order of Section 3 and proves every
   table entry is `±3H + b0*Q + b1*R`.
4. Prove completeness from the relevant `GoodOffset` conditions.
5. Prove cost 644/644 for fixed base and 32/32 for 2H/3H plus both tables.

**Acceptance:** table construction works under the same spec when Q+R=O or
Q=R; it never requests affine unshifted Q+R.

### T13 — Exhaustive offset bad-condition analysis

**Owner:** offset-analysis agent. **Depends on:** T01, T02 interfaces; agrees
with T04 and T12 on exact phase design.
**Owns:** `Math/OffsetConditions.lean`.

1. Define the unshifted fixed-base prefixes, ladder C_j, selected T_j and signs.
2. Define `GoodOffset` from finite points and required distinct-x conditions.
3. Prove same-x iff equal-or-negative for finite P-256 points.
4. Enumerate the 1039 equation slots from Section 5 with typed indices.
5. Prove every failure of admissibility implies one listed equation.
6. Check the final `elmTo` and both newly sequential P3 table additions.
7. Prove the no-extra-condition claims for 2H, 3H and the second ELM collision.

**Acceptance:** a coverage theorem covering every inverse denominator in the
implementation. Adjust the bound explicitly if the formal analysis discovers
an extra condition; never assume the source comment is a proof.

### T14 — Concrete safe-offset existence

**Owner:** offset-existence agent. **Depends on:** T02, T13.
**Owns:** `Math/OffsetCandidates.lean`.

1. Define `Fin 1040` candidates k -> [k+1]G.
2. Prove candidates distinct/finite and each map `[a]H_k` injective for every
   coefficient occurring in T13.
3. Instantiate `exists_avoiding_injective_equations` with the exact family.
4. Export `exists_goodOffset` for all valid Q,R,E,r,t.
5. Prove a finite candidate search succeeds, with a bound compatible with the
   executable witness generator.

**Acceptance:** no unresolved cardinality/injectivity hypotheses and no
assumption that H=G or H=2G always works.

### T15 — Joint ladder proof

**Owner:** ladder agent. **Depends on:** T07 semantic interface, T09, T10,
T12 shifted tables, T13 admissibility interface.
**Owns:** `Phases/JointLadder.lean`.

1. Define the phase as 255 returning steps and one final assertion step.
2. Prove the signed-offset prefix invariant with MSB-first consumption.
3. Preserve the on-curve/finite invariant and discharge each ELM premise.
4. Prove final-target semantics; combine it algebraically with the fixed-base
   result to obtain the three-term signature equation.
5. Prove completeness under `GoodOffset` and the target group equation.
6. Certify the 3070/3072 phase count.

**Acceptance:** induction handles j=0 and j=255 explicitly; no flattening of
the entire 256-step trace; sign cancellation proved at the actual final target.

### T16 — Honest seed construction and witness generation

**Owner:** witness-generation agent. **Depends on:** T03, T04, T06, T14.
**Owns:** `Witness/Generate.lean`, `Witness/Correctness.lean`.

1. Compute the standard verification point V from E,Q,r,s using certified
   arithmetic; for valid inputs take R=V.
2. Extract ry, canonical overflow, r bits, n-s bits and exact digest bits.
3. Select the first good candidate H via the bounded geometric search.
4. Produce the typed seed and prove its admissibility from standard validity.
5. Prove the actual sequential IR witness evaluation uses this seed and
   matches the values assumed in gadget completeness.
6. Export `generateSeed_complete` and combine generation with local
   completeness to obtain a concrete satisfying assignment.

**Acceptance:** finite-search success is proved, and malformed input failure
is handled explicitly. No full-constraint-satisfaction premise is smuggled
into the definition of an admissible seed.

### T17 — Whole-circuit assembly and final correctness

**Owner:** integration/proof agent. **Depends on:** T03, T07, T12, T15, T16.
**Owns:** `Main.lean` and top-level library exports.

1. Assemble bundled scalar, fixed-base, table and ladder phases.
2. Prove soundness by extracting their semantic specs, cancelling H, proving
   the x-lift condition and applying `standard_iff_signaturePoint`.
3. Prove admissible-hint completeness by composing local completeness.
4. Apply seed-existence/generation to prove global existential completeness.
5. Export `main_soundness`, `main_complete_with_seed`,
   `main_completeness`, and `main_accepts_iff_standard`.
6. State the equivalence at a concrete input embedding with disjoint auxiliary
   wire positions; keep generic-offset results where Clean requires them.

**Acceptance:** the two final directions refer to the actual circuit, not
only a pure arithmetic model. No assumptions remain on Q except those checked
by the circuit or entailed by the external standard predicate in completeness.

### T18 — Cost, R1CS, IR and channel certification

**Owner:** structural-proof agent. **Depends on:** stable bundled leaves;
final assembly from T17 for the exported statements.
**Owns:** `Cost.lean`, `R1CS.lean`, `WitnessIR.lean`; collaborates with T04.

1. Compose per-gadget/phase cost lemmas over loops/subcircuits.
2. Prove every assertion is one R1CS row, including guarded comparisons.
3. Prove witness operations use IR and channels/requirements are lawful.
4. Complete the fixed-hint causality theorem for the whole circuit.
5. Record exact allocations and rows; compare both against the phase ledger.
6. Tie cost certificates to the same exported main used by correctness.

**Acceptance:** proposed 4628/4634 is either certified or replaced with the
measured/proved actual result and a precise explanation of the delta.

### T19 — Standard-specific executable and adversarial regressions

**Owner:** validation agent. **Depends on:** T01; executable circuit and
generator as they become available.
**Owns:** `Tests/StandardECDSA/Main.lean`, test fixtures and generation scripts.

1. Use an independent standard P-256 verification implementation configured
   with matching digest and high-s semantics.
2. Test valid signatures, invalid keys, r/s=0 and out-of-range scalars,
   invalid limbs, altered digest, altered signature and infinity results.
3. Construct rare positive overflow fixtures: choose a finite R with
   `n <= x(R) < p`, set r=x(R)-n, choose nonzero s and E, then construct
   `Q=[r^(-1)]([s]R-[E]G)`; reject degenerate Q and verify independently.
   Random signing will not exercise this approximately 2^-128 branch.
4. Include valid Q=-G and Q+R=O fixtures, and exercise Q=R table construction.
   For Q+R=O, R=[k]G and E=k*(s+r) mod n gives a constructive route.
5. Exercise x=0 keys if such affine points exist; certify existence or
   impossibility rather than inventing an infeasible fixture.
6. Test exact digests 0,n-1,n,p-1,p,p+1,2^256-1 and distinct digests separated
   by p. These now have distinct limb inputs.
7. Test overflow/r boundary combinations, wrong bits, exceptional first H and
   successful retry, and mutations across seed/computed wire classes.

**Acceptance:** standard-valid exceptions are accepted. Do not reuse the
Longfellow accept/reject labels as the new oracle. Mutation checks recognize
legitimately unconstrained comparator quotients on inactive rows.

### T20 — Audit, export and contract-specific release verification

**Owner:** release/validation agent. **Depends on:** T17, T18, T19.
**Owns:** `Tests/StandardECDSA/Axioms.lean`, `StandardECDSA/Export.lean`,
new verification scripts/configuration and final documentation.

1. Extend the fail-closed audit with all final roots, group-order certificates,
   fixed-table certificates and safe-offset existence.
2. Implement a verifier entry point checking the new exact theorem types,
   input count, fixed-hint contract and certified cost.
3. Add positive and deliberately mismatched theorem/cost/spec fixtures for it.
4. Export the standard circuit's matrices and validate a satisfying assignment
   independently, including six-input binding and auxiliary-wire mutation.
5. Verify exporter support for bundled subcircuits and IR hints. Document
   matrix export as tested tooling unless export correctness is separately proved.
6. Measure clean project-build time, kernel replay and peak memory; record
   toolchain/dependency hashes and validation scope.
7. Produce a release summary with exact score and links to proof/audit roots.

**Acceptance:** explicit build targets include the new submission and audit;
default `lake build` alone is not the release check. Every required checker
has an observed result rather than an inherited historical log.

## 7. Scheduling and integration

### Dependency waves

| Wave | Tasks that can run concurrently |
|---|---|
| 0 | T00 |
| 1 | T01; then T02, T04 and T06 once shared interface types are frozen |
| 2 | T03 (after T02), T05, T10, T11, T13; T19 fixture design |
| 3 | T07, T08, T09 when affine interfaces are ready, T14; T18 leaf certificates |
| 4 | T12 fixed-base and table halves; T16; T19 executable harness |
| 5 | T15; integration of T18 certificates |
| 6 | T17, completed T18 and T19 |
| 7 | T20 |

Read the task-specific dependency lists as authoritative; waves are staffing
guidance, not permission to bypass a prerequisite. Generic algebra can proceed
against explicit hypotheses before their P-256 instances land, but final proofs
must discharge them.

### Critical paths

```text
T02 -> T03 -----------------------------> T17
T02 -> T13 -> T14 -> T16 ----------------> T17
T05 -> T08 -> T09 -> T12/T15 ------------> T17 -> T20
T02 -> T11 -> T12 -> T15 ----------------> T17
T06 -> T07 -----------------------------> T17
```

The highest-uncertainty tasks are T02 (concrete group certification), T13/T14
(complete offset coverage), and T04 (correct hint-aware framework contract).
Start these before spending substantial time on loop integration. No reliable
calendar estimate is justified until these three milestones are working.

### Worktree and file ownership rules

Use one worktree/branch per active task, based on the integration commit that
contains its prerequisites. Example, after the plan/scaffold is committed:

```sh
git worktree add /tmp/opencode/zkgolf-t06 -b agents/standard-ecdsa-t06 standard-ecdsa-proofs
git worktree add /tmp/opencode/zkgolf-t13 -b agents/standard-ecdsa-t13 standard-ecdsa-proofs
```

The coordinator owns `lakefile.lean`, central interfaces, `Main.lean`, shared
manifests and release configurations. Each agent owns only its packet's paths.
Publish shared theorem signatures/types before dependent tasks start. Review
interface changes with dependents, and merge small building commits in
dependency order. Do not share mutable build directories between worktrees.

### Handoff template for each agent

```text
Task: Txx from docs/standard-ecdsa-proof-plan.md
Base commit: <integration commit containing prerequisites>
Owned paths: <exact paths>
Required shared interfaces: <module names and theorem/type signatures>
Goal: <semantic result from task packet>
Required proofs: soundness, completeness, cost/structure as specified
Validation: build owned modules; audit new public proof roots; task-specific checks

Follow Clean AGENTS.md: bundle proof boundaries, call bundled subcircuits,
use semantic specs, start from the actual correctness theorem, and do not
increase maxHeartbeats. Do not add axioms or admit proof obligations.

Return:
- commit(s) and changed paths;
- exported theorem names and complete statements;
- build/audit commands and observed results;
- actual cost delta, if circuit rows changed;
- remaining assumptions and whether prerequisite tasks discharge them;
- integration notes and any interface changes required.
```

### Milestone gates

* **M0 — Reproduced source:** 9,267 reference reproduced, imports pinned.
* **M1 — Correct target:** specification and hint contract fixed; P-256 order
  proof and 1,039-exception coverage complete or explicitly blocking.
* **M2 — Standard circuit runs:** six inputs, overflow support, sequential
  shifted tables, exact digest binding; executable count compared to 9,262.
* **M3 — Local proof package:** all scalar/affine/ELM/mux/constants certified.
* **M4 — Complete prover:** concrete safe-offset theorem and seed generation.
* **M5 — End-to-end proof:** actual circuit acceptance iff standard ECDSA.
* **M6 — Release:** structural/cost proofs, audit, standard regressions and
  contract-specific verifier all pass.

## 8. Focused validation commands to add/use

Existing commands for the reference worktree:

```sh
lake build projected Baseline.Projected.Audit
lake exe projected --count-only
lake exe projected
lake exe projected --export Baseline/Projected/generated
python3 Baseline/Projected/check_matrices.py Baseline/Projected/generated
```

Proposed new targets/scripts (to be implemented by T00/T19/T20):

```sh
lake build StandardECDSA.Main StandardECDSA.Cost StandardECDSA.R1CS
lake build Tests.StandardECDSA.Axioms
python3 scripts/check_standard_ecdsa_axioms.py
lake exe standardEcdsaCheck
python3 scripts/check_standard_ecdsa_contract.py
python3 scripts/check_standard_ecdsa_matrices.py <export-directory>
```

Run targeted checks during each packet and the full new-instance suite at
integration milestones. Historical native C++/Rust checks remain useful for
the native reference, but cannot certify the broader standard acceptance set.

## 9. Source map for agents

From `optimized-proofs`:

* `Baseline/ECDSA_P256_Digest/Soundness/Range.lean` and
  `Completeness/Range.lean`: Boolean sums, grouped comparison and quotient proofs.
* `Baseline/ECDSA_P256_Digest/Soundness/Scalar.lean` and
  `Completeness/Scalar.lean`: nat/field bit reconstruction proof patterns.
* `Challenge/Utils/CostR1CS.lean`: existing subcircuit/loop cost and R1CS tools.
* `Challenge/Utils/WitgenIR.lean`: IR certification and the documented hint issue.
* `scripts/check_axioms.py`: fail-closed audit pattern.

From the pinned `circuit_baseline` revision:

* `Baseline/Projected/Offset.lean`: exact 9,267 circuit, hints, tables and loops.
* `Baseline/Projected/Algebra.lean`: ELM identities and denominator redundancy.
* `Baseline/Projected/AffineBridge.lean`, `ProjectiveBridge.lean`: group semantics.
* `Baseline/Projected/P256Algebra.lean`, `P256Bridge.lean`: reusable P-256 facts;
  the latter's final Longfellow equivalence is not the new specification.
* `Baseline/Projected/OffsetExistence.lean`: generic counting theorem.
* `Baseline/Projected/Check.lean`, `Export.lean`, `check_matrices.py`: reference
  diagnostics/export logic to adapt, not whole-circuit correctness proofs.
* `docs/ecdsa-optimization-handoff.md`: proposal for standard-complete migration
  and its original approximate 9,262 estimate.

The plan's numerical work was a source-level count/inequality calculation.
No new Lean theorem, standard circuit, or reference executable was built during
planning; reproduction and implementation results must be recorded by the tasks
above.
