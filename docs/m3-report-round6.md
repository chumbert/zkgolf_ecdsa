# M3 report — round 6

## Timing

| | value |
|---|---|
| `date -u +%s` before | **not captured** (deviation — see below) |
| `date -u +%s` after | `1795023420` |
| last observed clock reading before this round (round-5 after) | `1795021847` |
| elapsed_seconds (after − round-5 after) | **1573** |

**Deviation, stated explicitly:** the mandatory `date -u +%s` *before* this round
was not run before starting work. The only defensible elapsed figure is
`1795023420 − 1795021847 = 1573 s`, measured from the round-5 after-value. This
is an upper bound on round-6 work only if no wall-clock time passed between the
round-5 report and the start of round 6, which is not guaranteed.

## What was proved

### `StandardECDSA/Gadgets/Semantics5.lean` (new, 383 lines, green)

`mux4` — the variable four-way point mux — is now a fully bundled gadget. This
was the last outstanding gadget family.

**Offset independence of the local length** (the obstruction reported in round 5):

* `mux4A1 … mux4A6`, `mux4Off4` — the six `sel` arguments as named expressions.
  The fourth `sel`'s offset is `n + matLen A1 + matLen A2 + matLen A3(n)`, i.e.
  the y-coordinate block starts *after* all three x-coordinate muxes; getting
  this wrong was the first failed attempt.
* `VarEq.neg`, `VarEq.sub` (added to `Gadgets/VarShape.lean`) — `VarEq` is a
  congruence for `-`, which desugars to `add a (mul (const (-1)) b)`.
* `mux4A3_varEq`, `mux4A3_matLen`, `mux4A6_varEq`, `mux4A6_matLen` — the two
  offset-dependent arguments have `VarEq`-equal instances at every offset, hence
  equal `deg` and equal `matLen`.
* `mux4Len` — the offset-free local length, written as the sum of the six
  `matLen`s at offset `0`.
* `mux4_localLength` — the local length at an arbitrary offset, in the same
  named form.
* `mux4Len_eq` — `(mux4 …).localLength n = mux4Len …` for every `n`.

**Structure**

* `mux4Out`, `mux4_output` — the output pair at offset `n`.
* `mux4OpsExplicit` — the `do`-block as an explicit `ExplicitCircuit.from_bind`
  chain over `matExplicit`, used only to inherit `subcircuitsConsistent` and
  `channelsLawful` (the `ExplicitCircuit` defaults do not fire for `mux4`).
* `mux4Explicit` — `ExplicitCircuit (mux4 …)` with the constant `localLength`.
* `mux4Main`, `mux4Family`, `ExplicitCircuits.IsElaborated`,
  `ElaboratedCircuit Fp (fields 10) (ProvablePair field field) mux4Main`.

**Semantics**

* `mux4A1_eval … mux4A6_eval` — evaluation of the six `sel` arguments.
* `mux4Spec` — `∃ c0 c1, i[0] = c0 ∧ i[1] = c1 ∧ out = entry (c0 + 2·c1)`.
* `mux4Main_output`.
* `mux4Main_soundness` — from an arbitrary satisfying assignment and Boolean
  `b0`, `b1`, the output is the selected entry. The six `mat` rows are peeled
  with `Operations.forAllNoOffset_append` and converted to
  `env (matOut e n) = eval e` by `mat_eval_gen`.
* `mat_complete'` — `mat_complete` restated on `(mat e n).2`.
* `mux4Main_completeness` — six `ulwc_append` splits plus `mat_complete'`.
* `requirementsChannelsLawful_append` — `RequirementsChannelsLawful` composes
  over `++` when both channel lists are empty (Clean provides no such lemma).
* `mux4Circuit : FormalCircuit Fp (fields 10) (ProvablePair field field)`.

Cost and R1CS certificates for `mux4` were already in place from round 2
(`mux4_cost` in `Gadgets/Cost.lean`, `isR1CSCirc_mux4` in `Gadgets/R1CS.lean`).

## Checks (observed)

```
$ lake build
Build completed successfully (17893 jobs).

$ lake build StandardECDSA.Main
Build completed successfully (8996 jobs).

$ grep -rn "sorry" StandardECDSA/
(no output; exit 1)

$ lake exe standardEcdsaCheck --count-only
Standard P-256 ECDSA circuit (6 fixed inputs)
allocations=4628 rows=4634 score=9262

$ lake exe standardEcdsaCheck --comparator
allocations=4628 rows=4634 score=9262
comparator: 20 cases, 0 failures

$ python3 scripts/check_axioms.py
Tests/Axioms.lean: 26 roots passed the permitted-axiom audit
```

Count is unchanged at **4628 / 4634 = 9262**, matching the plan budget exactly.

## Build errors

None in the committed state. (Intermediate failures during the round are
described under "What was proved"; all were resolved.)

## Files changed

```
$ git status --short
(clean)

$ git show --stat --oneline a77b61e
a77b61e M3: bundle mux4 (offset-free localLength via VarEq, semantic spec, soundness, completeness, cost/R1CS)
 StandardECDSA/Gadgets/Semantics5.lean | 383 ++++++++++++++++++++++++++++++++++
 StandardECDSA/Gadgets/VarShape.lean   |   7 ++
 2 files changed, 390 insertions(+)
```

## M3 status: NOT complete

Bundled gadget families (semantic spec + soundness + completeness + cost +
R1CS): `sel`, `muxConst4`, `affAdd`, `affDouble`, `elm`, `elmTo`, `isOnCurve`,
`pointEquality`, **`mux4`** — **9 of 9 gadget families**.

Still outstanding for the M3 gate:

### (c) Comparator semantic specs — `assertLtOrderOf`, `assertLtOrderGuardedOf`

Not started. The obstruction is mathematical, not mechanical: the grouped
comparison argument needs

1. `missing` and `runSum` as *natural* counts (`Σ_{k ≥ lo, bound_k = 1} (1 - a_k)`
   and `Σ_{k = lo}^{hi} a_k`), each at most 256, together with the cast lemma
   `(Σ (1 - env (a k)) : Fp) = ((Σ (1 - aNat k) : Nat) : Fp)` under the Boolean
   hypothesis, so that `missing = 0` in `Fp` implies `missing = 0` in `Nat`
   (no field wraparound);
2. the invariant `S(lo) ≤ B(lo) ∧ (missing = 0 ↔ S(lo) = B(lo))` where
   `S(lo) = Σ_{k ≥ lo} 2^(k-lo) a_k` and `B(lo) = Σ_{k ≥ lo} 2^(k-lo) bound_k`,
   maintained over `boundRunsOf bound`;
3. the inactive-overflow branch: with `guard = 0` the first factor is
   `missing + 1 ∈ [1, 257]`, so a quotient exists for every Boolean bit vector —
   this is the completeness direction and needs `1 ≤ missing + 1 ≤ 257 < p`.

`Math/ConstantBounds.lean` currently contains only the run-count certificates
(`zero_runs_n_minus_one = 34`, `zero_runs_p_minus_n_minus_one = 34`,
`zero_bits_* = 90 / 198`); none of the comparator soundness/completeness
mathematics is there yet.

### (d) Phase cost certificates

Attempted this round; **reverted** because the required `ConstantLength`
obligations are not yet discharged. Exact diagnosis:

* `for i in [0:128]` desugars to `forIn [:128] ep fun i __s => …`, and
  `Challenge.CostR1CS` has **no** `CostIs` lemma for `forIn` over a `List`. The
  available loop lemmas are `CostIs.forEach` (over a `Vector`),
  `CostIs.mapFinRange` and `CostIs.foldlRange`.
* Restructuring `fixedBase` to `Circuit.foldlRange 128 ep0 body` compiles, but
  `foldlRange` demands `Circuit.ConstantLength (fun x : Pt × Fin 128 => body x)`,
  and that obligation reduces to
  `matLen (mul (eb.getD (2 * i) (cst 0)) (eb.getD (2 * i + 1) (cst 0)))`
  being independent of `i`. It is not: `matLen` branches on
  `deg (eb.getD k (cst 0))`, which is unknown for symbolic `k`. The fix is to
  add `heb : ∀ k, deg (eb.getD k (cst 0)) = 1` as a parameter of `fixedBase`
  (and discharge it at the `Main.lean` call site, where `eb` is built from
  `witnessField` outputs).
* Restructuring `jointLadder` into `foldlRange 255` + a final `elmTo` step
  compiles and gives the right 3070/3072 split, but its `ConstantLength`
  obligation additionally needs `mux4Len` invariance under the alternating
  `tables.plus` / `tables.minus` choice. That is true — `degree (mul a b) =
  degree a + degree b`, so `deg` is preserved by `negPt`, and the two tables'
  entries have pairwise equal `deg` — but it needs a `mux4Len` congruence lemma
  in the eight `deg`-equalities of the four points, which was not written.

Both restructured files were reverted so the tree stays green and the count
stays 4628/4634 = 9262.

### (e) Phase semantic specs

Not started. This is the largest remaining item:

* `FixedBase`: 128-step induction over the window invariant
  `ep_k = H - S + Σ_{i<k} [(4 + d_i)·4^i]G`, concluding `ep_128 = H + [E]G`.
* `ShiftedTables`: entries `= ±3H + b0·Q + b1·R` in table order `rBit + 2·tBit`,
  working when `Q + R = O` or `Q = R` (never requesting affine unshifted
  `Q + R`).
* `JointLadder`: the signed-offset prefix invariant with MSB-first consumption,
  255 returning steps plus the final `elmTo` assertion against `-ep`, carrying
  on-curve/finite facts through the invariant.

## Next milestone I would attempt

Continue **M3 item (c)** — the comparator semantic specs — since it is the last
gadget-level item and its mathematics is self-contained (no dependence on the
phase design). Concretely: add the `Nat`-valued `missing`/`runSum` counts and
the `Fp`-cast lemma to `Math/ConstantBounds.lean`, then prove
`ltLoop_soundness` / `ltLoop_completeness` and `ltLoopGuarded_*` by induction
over `boundRunsOf bound`, then bundle
`assertLtOrderMain` / `assertLtOrderGuardedMain` as `FormalCircuit`s.

After that, (d) with the `deg`-hypothesis fix described above, then (e).
