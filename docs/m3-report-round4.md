# M3 round 4 — gadget semantic bundling (affDouble, elm, elmTo)

Timing: before `1795011367`, after `1795018253`, elapsed_seconds = **6886**.

## What was proved (new, all in `StandardECDSA/Gadgets/Semantics3.lean`)

### `affDouble` (T08, doubling half)
* `affDoubleMain`, `ElaboratedCircuit` instance
* `affDoubleMain_output` — output at `(.var ⟨n + matLen (i[0].mul i[0]) + 1⟩, .var ⟨n + matLen (i[0].mul i[0]) + 2⟩)`
* `affDoubleEqs`, `affDoubleEqs_group` — the four rows give
  `∃ hR : NS out.1 out.2, some out.1 out.2 hR = 2 • some i[0] i[1] hA`
  (via `Affine.Point.add_self_of_Y_ne` + `two_nsmul`; the output on-curve proof is
  *derived*, not assumed)
* `affDoubleSpec`, `affDoubleAssumptions` (`NS i[0] i[1] ∧ 2 * i[1] ≠ 0`)
* `affDoubleMain_soundness` — from an arbitrary satisfying assignment; the `xx` row is
  discharged by `mat_eval_gen` + `mat_output_eq` + `mat_localLength_eq`
* `affDoubleMain_completeness` — from the honest witnesses; the slope row is closed by
  `field_simp` with `2 * i[1] ≠ 0`
* `affDoubleCircuit : FormalCircuit Fp (fields 2) (ProvablePair field field)`

### `elm` (T09)
* `ns_equation` — `NS x y → y^2 = x^3 + params.a*x + params.b`
  (via `Affine.equation_iff_nonsingular` + `Affine.equation_iff`)
* `elmMain`, instance, `elmMain_output` (`rfl`: `(.var ⟨n+4⟩, .var ⟨n+5⟩)`)
* `elmEqs` (six rows incl. the guarded first inverse), `elmEqs_group` — the rows give
  `∃ hR, some out.1 out.2 hR = 2 • some i[0] i[1] hA + some i[2] i[3] hB`
  via `AffineBridge.elm_eq_group`; the first denominator is *derived* from the enforced
  inverse row (`(i[2]-i[0]) * inv1 = 1`), the second from `elm_second_denominator_ne`
  inside `elm_eq_group`
* `elmXu` — the `x`-coordinate of `P+Q` as computed from the inputs
* `elmSpec`, `elmAssumptions` (`NS, NS, i[2]-i[0] ≠ 0, i[0] - elmXu i ≠ 0`)
* `elmMain_soundness`, `elmMain_completeness`
  (completeness uses `i[0] - elmXu i ≠ 0` to invert the second denominator — **no
  circular use of the third ELM equation**)
* `elmCircuit : FormalCircuit Fp (fields 4) (ProvablePair field field)`

### `elmTo` (T09, assertion form)
* `elmToMain`, instance
* `elmToL1`, `elmToXu`, `elmToL2` — the three computed ELM quantities
* `elmToSpec` — `∃ hA hB hT, 2 • some i[0] i[1] hA + some i[2] i[3] hB = some i[4] i[5] hT`
* `elmToAssumptions` — `NS ×3`, `i[2]-i[0] ≠ 0`, `i[0] - elmToXu i ≠ 0`, plus the two
  target coordinate equations (the assertion's own content)
* `elmToMain_soundness` — `FormalAssertion.Soundness`; the target is *not* re-allocated,
  the two final rows are matched against `input[4]`, `input[5]`
* `elmToMain_completeness` — `FormalAssertion.Completeness`
* `elmToAssertion : FormalAssertion Fp (fields 6)`

## Checks (observed)

```
lake build StandardECDSA.Main      -> Build completed successfully (8996 jobs)
lake build                         -> Build completed successfully (17893 jobs)
grep -rn "sorry" StandardECDSA/    -> exit 1 (zero hits)
lake exe standardEcdsaCheck --count-only -> allocations=4628 rows=4634 score=9262
lake exe standardEcdsaCheck --comparator -> comparator: 20 cases, 0 failures
lake exe standardEcdsaCheck        -> smoke test: all R1CS assertions hold with H = [1]G
```

Count unchanged at **4628 / 4634 = 9262** (no circuit rows changed; only proofs added).

## Files changed

```
 M StandardECDSA/Gadgets/Semantics3.lean   (+363)
```

`StandardECDSA/Gadgets/Scratch1.lean` (scratch) was created and deleted within this round.

## Still open for M3 item (3)

* (1) `mux4` elaboration (`ElaboratedCircuit.withData` with explicit `localLength` +
  `data_eq`; needs `matLen (matOut e n) = matLen e`).
* (2) `isOnCurve` / `pointEquality` (`assertZeroLazy` recurses over `flat 1 e`, stuck for
  opaque `e`).
* (c) comparator semantic specs (`assertLtOrderOf` / `assertLtOrderGuardedOf`), incl. the
  inactive-overflow completeness branch.
* (d) phase cost certificates (FixedBase 644/644, 2H/3H+tables 32/32, JointLadder
  3070/3072) after restructuring the `[0:128]` / `[0:256]` loops.
* (e) phase semantic specs (FixedBase `ep = H + [E]G`; ShiftedTables
  `±3H + b0·Q + b1·R`; JointLadder signed-offset invariant + final `elmTo` target).

Bundled so far: `sel`, `muxConst4`, `affAdd`, `affDouble`, `elm`, `elmTo`
(6 of the 8 gadget families; `isOnCurve`/`pointEquality` and the comparators remain).
