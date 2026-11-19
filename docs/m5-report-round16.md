# M5 report (round 16) — M5-2b finished, M5-2c delivered

## Timing

- before: `1795054089`
- after: `1795057694`
- elapsed_seconds: **3605**

## What was proved

### M5-2b (finished this round)

`StandardECDSA/Main.lean`:

- `jointLadderFold_ops_localLength` — `Operations.localLength` of the 255-step
  fold's operations is `3060` (the `Operations`-level companion of
  `jointLadderFold_localLength`, needed because `ulwc_append` produces the
  offset as `n + Operations.localLength a`).
- `jointLadder_foldl_completeness` — the fold's completeness splits into the
  255 per-step obligations.
- `@[irreducible] def jlAcc` + `jlAcc_eq` — seal for the fold accumulator.
- `@[irreducible] def jlOut` + `jlOut_eq` — seal for the fold *output*
  (`(foldlRange …).output n`), which is the accumulator of the final step.
- `jointLadderBody_localLength`, `jointLadderBody_complete`,
  `jointLadderFinal_complete`, `selW_complete`, `mux4W_complete`,
  `elmCore_complete`, `elm_complete`, `elmTo_complete`.
- **`jointLadder_complete`** — completeness of the 255-step returning ladder
  plus the final `elmTo` step, under the distinct-x hypotheses.

### M5-2c (delivered this round)

`StandardECDSA/Main.lean`:

- `off1 … off8` — the nine stage offsets of `main` as named definitions.
- `main_ops'` — `main`'s operations split into the nine stages with the
  offsets named (proved from `main_ops` by `rfl`).
- `structure CompleteWitness (inp) (env) (n) : Prop` — the witness facts the
  honest prover must supply: overflow Boolean, the three on-curve equations,
  `r ≠ 0`, `t = n - s ≠ 0`, the three Boolean bit vectors, the four
  digest/scalar bindings, the two order bounds and the guarded lift bound, the
  fixed-base denominators (`hfb0`, `hfb`), the shifted-table denominators
  (`hshy`, `hs1 … hs5`), and the ladder denominators (`hj1`, `hj2`, `hjf1 …
  hjf4`).
- **`main_complete_with_seed`** — completeness of the actual circuit `main`
  from `UsesLocalWitnessesCompleteness` plus `CompleteWitness`, by composing
  the nine phase completeness lemmas (`seedPhase_complete`,
  `curvePhase_complete`, `nonzeroPhase_complete`, `bitsPhase_complete`,
  `bindPhase_complete`, `cmpPhase_complete`, `fixedBase_complete`,
  `shiftedTables_complete`, `jointLadder_complete`).
- `soundness_of_completeness` — `ConstraintsHold.Completeness → Soundness`
  when the operations list has no lookups and no subcircuits (via
  `constraintsHold_completeness_iff_forall_mem` /
  `constraintsHold_soundness_iff_forall_mem`).
- **`main_completeness`** — existential completeness: an honest witness
  environment yields `∃ env, ConstraintsHold.Completeness env ((main inp).operations n)`.
- **`main_accepts_iff_standard`** — for an honest witness environment,
  `ConstraintsHold.Soundness penv ((main inp).operations n) ↔ standardVerify …`
  over the actual circuit `main`.

All four M5 exports are present and refer to the actual circuit `main`:

| theorem | file:line |
|---|---|
| `main_soundness` | `StandardECDSA/Main.lean:1248` |
| `main_complete_with_seed` | `StandardECDSA/Main.lean:2254` |
| `main_completeness` | `StandardECDSA/Main.lean:2287` |
| `main_accepts_iff_standard` | `StandardECDSA/Main.lean:2314` |

## Checks

```
$ lake build StandardECDSA.Main
Build completed successfully (9020 jobs).

$ grep -rn "sorry" StandardECDSA/
(no output, exit 1)

$ lake exe standardEcdsaCheck --count-only
Standard P-256 ECDSA circuit (6 fixed inputs)
allocations=4628 rows=4634 score=9262

$ #print axioms
'StandardECDSA.main_soundness'          depends on axioms: [propext, Classical.choice, Quot.sound]
'StandardECDSA.main_complete_with_seed' depends on axioms: [propext, Classical.choice, Quot.sound]
'StandardECDSA.main_completeness'       depends on axioms: [propext, Classical.choice, Quot.sound]
'StandardECDSA.main_accepts_iff_standard' depends on axioms: [propext, Classical.choice, Quot.sound]
'StandardECDSA.soundness_of_completeness' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No build errors. No `sorry`. Cost unchanged at 4628/4634 = 9262.

## Files changed

```
 M StandardECDSA/Main.lean
```

## Remaining assumptions (honest gaps, not `sorry`)

1. **`CompleteWitness` denominators (T13 instantiation).** The distinct-x
   conditions of the fixed-base, shifted-table and ladder phases are bundled
   as explicit hypotheses of `CompleteWitness`. Discharging them from
   `Math.OffsetConditions.GoodOffset` requires instantiating the abstract
   `BadFamily` with the concrete 1,039-slot family of the circuit's affine
   operations. That instantiation has been flagged as blocking since M1 and is
   still open. `GoodOffset` itself is proved to be satisfiable
   (`exists_goodOffset`, `generateSeed_goodOffset`); what is missing is the
   bridge `GoodOffset H hH fam → <the concrete denominators are nonzero>`.
2. **Honest witness environment (T16).** `main_completeness` and
   `main_accepts_iff_standard` take the existence of a `ProverEnvironment`
   with `UsesLocalWitnessesCompleteness` and `CompleteWitness` as a
   hypothesis. Constructing the concrete 4,634-wire environment (the honest
   prover's sequential witness evaluation) is T16 work; `generateSeed_complete`
   already supplies the seed half of it.
3. **`hl` / `hs`.** `((main inp).operations n).shallowLookups = []` and
   `((main inp).operations n).subcircuits = []` are structural facts about
   `main`'s operation list, passed as hypotheses to
   `main_accepts_iff_standard`. They are true (the circuit has no lookups and
   no subcircuits) but not yet proved in Lean; a `NoLookupSub` predicate
   preserved by `++` and by each gadget/phase would close them.

## Next milestone

M6 (T18 whole-circuit `Cost`/`R1CS`/`WitnessIR`/`HintCausality` certificates
tied to `main`; T19 `Tests/StandardECDSA/Main.lean` regressions; T20
`Tests/StandardECDSA/Axioms.lean` + `scripts/check_standard_ecdsa_axioms.py` +
contract/matrix scripts).
