# M3 round 14 report — item (e3-final) fixed-base phase: root cause found and fixed

## Timing
- before = 1795031392
- after  = 1795036090
- elapsed_seconds = 4698

## Root cause of the `whnf` blow-up (diagnosed this round)

`Circuit F α := ℕ → α × List (Operation F)` and

```lean
def Circuit.bind (f) (g) : Circuit F β := fun n =>
  let (b, ops') := g (f n).1 (n + Operations.localLength (f n).2)
  (b, (f n).2 ++ ops')
```

Because `bind` **destructures** `g (f n).1 …` before returning the pair,
`whnf ((f >>= g).operations n)` must reduce `g (f n).1 …` to a pair.  For
`fixedBase` the continuation is the 128-window `foldlRange`, so every defeq
check that mentions `(fixedBase h eb).operations n` unfolded the whole fold.
That is the `deterministic timeout at whnf` / `maximum recursion depth` seen in
rounds 12–13.  It is *not* a mathematical gap and *not* `mulG`.

## Structural fixes applied

1. **`fixedBase` rewritten from a `do` block to an explicit lambda**
   (`StandardECDSA/Phases/FixedBase.lean`):

   ```lean
   def fixedBase (h : Pt) (eb : Vector E 256) : C Pt := fun n =>
     let ops0 := (affAdd h (cst shiftX, cst (-shiftY)) n).2
     let r := Circuit.foldlRange 128 (affAdd h (cst shiftX, cst (-shiftY)) n).1
       (fixedBaseBody eb fixedTables) (fixedBaseBody_constantLength eb fixedTables)
       (n + Operations.localLength ops0)
     (r.1, ops0 ++ r.2)
   ```

   Now `(fixedBase h eb).operations n` reduces to `ops0 ++ r.2` in one step,
   without destructuring the fold.  Semantics, operations, output and
   localLength are unchanged (count still 4628/4634 = 9262).

2. **`shiftX` / `shiftY` marked `@[irreducible]`** so `whnf` never unfolds the
   256-bit scalar multiplication `mulG` behind the shift coordinates.
   `shiftX_eq` / `shiftY_eq` are recovered with `with_unfolding_all rfl`.

3. **`fixedBase_cost` re-proved** for the new definitional form
   (`StandardECDSA/Phases/Cost.lean`): `intro n`, `CostIs.foldlRange`,
   `Challenge.CostR1CS.Lemmas.operationCount_append`, `affAdd_cost`, `decide`.
   Still `⟨644, 644⟩`.

## What was proved

| Theorem | File | Statement |
|---|---|---|
| `shiftX_eq`, `shiftY_eq` | `Phases/FixedBase.lean` | `shiftX = fixedShift.1`, `shiftY = fixedShift.2` |
| `fixedBase_ops` | `Phases/FixedBaseSemantics.lean` | `(fixedBase h eb).operations n = (affAdd h (cst shiftX, cst (-shiftY))).operations n ++ (foldlRange 128 …).operations (n + 4)` |
| `fixedBase_out` | `Phases/FixedBaseSemantics.lean` | `(fixedBase h eb).output n = (foldlRange 128 …).output (n + 4)` |
| `fixedBase_cost` | `Phases/Cost.lean` | `CostIs (fixedBase h eb) ⟨644, 644⟩` |

Plus everything already committed in `9ce2f9c`: `toAffineLift_add`,
`toAffineLift_zero`, `digitOf`, `digitOf_eq`, `winSum`, `winSum_succ`,
`digestNat`, `winSum_128`, `fbMux`, `fixedBaseBody_eq`, `fbInv`,
`fin_foldl_inv`, `foldlAcc_eq`, `fbStep`.

## Remaining obstruction for `fixedBase_spec` (verbatim)

`fixedBase_spec` is still **not** proved.  The split of `hc` now works in
isolation, but the *second* component fails:

```
error: StandardECDSA/Phases/FixedBaseSemantics.lean:391:4: maximum recursion depth has been reached
```

at

```lean
  have hc2 : ConstraintsHold.Soundness env
      ((Circuit.foldlRange 128 ((affAdd h (cst shiftX, cst (-shiftY))).output n)
        (fixedBaseBody eb fixedTables)
        (fixedBaseBody_constantLength eb fixedTables)).operations (n + 4)) :=
    (Operations.forAllNoOffset_append.mp hc').2
```

i.e. any defeq check that mentions `(Circuit.foldlRange …).operations (n + 4)`
unfolds `foldlRange` into a 128-step `Fin.foldl`.  With
`set_option maxRecDepth 10000` the same site becomes
`deterministic timeout at whnf, maximum number of heartbeats (200000)`.
Passing `as`/`bs` explicitly to `Operations.forAllNoOffset_append`, using
`soundness_bind` directly, and rewriting with a `rfl` equation for `fixedBase`
all fail at the same place.  `maxHeartbeats` was **not** raised.

The same fix (explicit-lambda phase definitions) will be applied to
`shiftedTables` and `jointLadder` before their specs are attempted, since they
have the identical `do`-block shape.

## Checks

- `lake build` → `Build completed successfully (17893 jobs)`
- `lake build StandardECDSA.Main` → `Build completed successfully (9013 jobs)`
- `grep -rn "sorry" StandardECDSA/` → exit 1 (zero hits)
- `lake exe standardEcdsaCheck --count-only` → `allocations=4628 rows=4634 score=9262`

## Files changed

```
 M StandardECDSA/Phases/Cost.lean
 M StandardECDSA/Phases/FixedBase.lean
```

## Next milestone

M3 item (e4) `JointLadder.Spec` (with the explicit-lambda restructure first),
then M4.
