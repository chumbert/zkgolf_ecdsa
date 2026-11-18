# M3 (round 3) — semantic bundling, item (3)

Timing: before `1795009411`, after `1795011315`, elapsed **1904 s**.

## What was done

### The critical unblock: `ExplicitCircuit` instances for `mat` and stuck `ite`

`elaborate_circuit` could not elaborate any gadget that calls `mat`, because
`mat` is a *recursive* circuit and the tactic can only unfold a wrapper whose
argument is already a constructor application.  Two new files fix this:

* `StandardECDSA/Gadgets/MatExplicit.lean`
  * `matLen : E → ℕ` — local length of `mat e`.  Deliberately **offset-free**:
    the branch condition `deg a = 0 ∨ deg b = 0` is a property of the expression
    alone, and Clean's `ExplicitCircuits.IsElaborated` side condition requires
    offset-independence.
  * `matOut : E → ℕ → E`, `matOps : E → ℕ → Operations Fp` — output expression
    and operation list, mirroring `mat` structurally.
  * `mat_localLength_eq`, `mat_output_eq`, `mat_operations_eq`,
    `matOps_localLength`, `matOps_subcircuitsConsistent`,
    `matOps_channelsLawful`, `mat_subcircuitsConsistent`, `mat_channelsLawful`.
  * `matExplicit : ExplicitCircuit (mat e)`, tagged
    `@[instance_reducible, explicit_circuit_constructor]`, plus a plain
    `instance (e : E) : ExplicitCircuit (mat e)`.
  * Projection-level helper lemmas `bind_fst`, `bind_snd`, `witnessField_fst`,
    `witnessField_snd`, `assertZero_fst`, `assertZero_snd`, `pure_fst`,
    `pure_snd`, `map_fst`, `map_snd` — `Expression.eval`-style accessors are
    `brecOn`-compiled and do not reduce, so the proofs work at the `.1`/`.2`
    level instead.

* `StandardECDSA/Gadgets/IteExplicit.lean`
  * `ExplicitCircuit.from_ite` — an `ExplicitCircuit` instance for
    `if c then A else B` when `c` is stuck.  Needed because `mat`'s allocation
    branch is `if deg a = 0 ∨ deg b = 0` and both factors are opaque at
    elaboration time.
  * `channelsWithGuarantees` is the **union** of the two branches' metadata
    (still a lawful superset) so that it stays syntactically offset-independent.
  * `channelsLawful_mono` — `ChannelsLawful` is monotone in the channel list.

### Semantic soundness of `mat`

`StandardECDSA/Gadgets/MatSemantics.lean`:

* `mat_eval_gen (e : E) : ∀ n env c, (∀ x, c.assert x → eval env x = 0) →
  forAllNoOffset c ((mat e) n).2 → eval env (matOut e n) = eval env e`
  — **any** assignment satisfying the rows of `mat e` makes the output
  expression evaluate to `e`.  Phrased for an arbitrary `ConditionNoOffset` so
  it applies both to `ConstraintsHold` and to the `ConstraintsHold.Soundness`
  condition produced by `circuit_proof_start`.

## What now elaborates (verified by scratch files)

`sel`, `muxConst4`, `affAdd`, `affDouble`, `elm`, `elmTo` all get
`ElaboratedCircuit` instances from `unfold …; elaborate_circuit`.

## What still does not

1. **`mux4`** — `elaborate_circuit` fails in the `localLength` normalisation
   step: `mux4`'s local length is `matLen e₁ + matLen e₂ + …` where `e₂` contains
   `matOut e₁ n`, so it is only *semantically* offset-independent, not
   syntactically.  `elaborate_circuit` normalises `localLength` at offset `0` and
   then needs `localLength n = localLength 0` by `rfl`.  Fix requires
   `ElaboratedCircuit.withData` with an explicit constant `localLength` and a
   `data_eq` proof — per gadget.
2. **`isOnCurve`, `pointEquality`** — both call `assertZeroLazy`, which recurses
   over `flat 1 e`.  For an opaque `e`, `flat 1 e` is stuck, so neither
   `localLength` nor `operations` can be computed: an `ExplicitCircuit
   (assertZeroLazy e)` instance is not expressible without a decidable
   `flat`-shape test.
3. **Phase cost certificates (item d)** and **phase semantic specs (item e)** —
   blocked on (1) and (2): `FixedBase`, `ShiftedTables` and `JointLadder` all
   call `mux4`/`muxConst4`/`assertZeroLazy`/`isOnCurve`.
4. **Gadget semantic bundling for `sel`/`affAdd`/…** — the `Soundness` statement
   shape is now reachable (`mat_eval_gen` + `show` on
   `ElaboratedCircuit.output`), but the final `Vector.map` bookkeeping
   (`(Vector.map f v)[i] = f (v[i])` for `h_input`) did not close with
   `simp [Vector.getElem_map]` in the budget available; this is a small,
   purely mechanical remaining step.

## Checks

```
lake build                                  -> Build completed successfully (17893 jobs)
lake exe standardEcdsaCheck --count-only    -> allocations=4628 rows=4634 score=9262
lake exe standardEcdsaCheck --comparator    -> comparator: 20 cases, 0 failures
grep -rn "sorry" StandardECDSA/             -> exit 1 (zero hits)
```

## Commits

* `a48b745` M3: ExplicitCircuit instances for mat and stuck ite branches
* `2b81c7c` M3: mat_eval semantic soundness lemma
