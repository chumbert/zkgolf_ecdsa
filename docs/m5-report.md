# M5 report (T17 whole-circuit assembly) — PARTIAL, round 2

Timing: before = `1795052259`, after = `1795052705`, elapsed_seconds = **446**.

## Status

M5 is **not** complete. The `fixedBaseOut` seal (proposed last round) is implemented,
builds green, and **removes the `fixedBase` unfolding problem entirely**. One
elaboration obstacle remains: the `hc` argument of `jointLadder_spec`.

## Landed this round (committed, builds green)

| File | Change |
|---|---|
| `StandardECDSA/Phases/FixedBase.lean` | new `@[irreducible] def fixedBaseOut (h : Pt) (eb : Vector E 256) (n : Nat) : Pt` = the 128-window fold's output, plus `fixedBaseOut_eq`. `fixedBase`'s body now returns `(fixedBaseOut h eb n, ops0 ++ r.2)`, so `(fixedBase h eb n).1` whnf-reduces to the *stuck* term `fixedBaseOut h eb n` in one step. |
| `StandardECDSA/Phases/FixedBaseSemantics.lean` | `fixedBase_out` re-proved as `show fixedBaseOut h eb n = _; exact fixedBaseOut_eq h eb n`. |

Verified:

```
lake build StandardECDSA.Main      -> Build completed successfully (9020 jobs)
grep -rn "sorry" StandardECDSA/    -> exit 1 (zero hits)
lake exe standardEcdsaCheck --count-only
  -> allocations=4628 rows=4634 score=9262
```

## What now compiles in the draft of `main_soundness` (`/tmp/s32.lean`)

Everything except the `hc` argument of `jointLadder_spec`:

- `soundness_append9` split into `h1 … h9`; the six scalar/curve phase soundness
  applications; `fixedBase_dx` + `fixedBase_spec`.
- `hEpP : some (eval ((fixedBase …).output n6).1) (eval ((fixedBase …).output n6).2) hnsEp
  = some (eval hxE) (eval hyE) hHns + toAffineLift (digestNat env eb • Gpt)` — now
  literally `hEp`, because the seal makes the two sides cheaply defeq.
- `h8'` via `Eq.mp (congrArg …) (shiftedTables_snd …) h8`; `shiftedTables_hy`,
  `shiftedTables_dx`, `shiftedTables_htab`.
- `hacc0`, `hT`, `hneg` (all in terms of `TGT = ((fixedBase … n6).1.1, -((fixedBase … n6).1.2))`,
  which is now cheap).
- the `main_group_algebra` call with `ep`/`target`/`hEpP`/`hTgt`/`hneg`.
- `x_mod_order_iff_lift` and the final `standard_iff_signaturePair` assembly.

## Exact obstruction (verbatim)

```
/tmp/s32.lean:494:352: error: maximum recursion depth has been reached
```

at

```lean
have h9t : ConstraintsHold.Soundness env
    ((jointLadder (hxE, -hyE) ((shiftedTables … n7).1) (bitsPhase n3).1.rb
        (bitsPhase n3).1.sb
        (((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.1,
         -((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.2) n8).2) := h9
```

i.e. the defeq check between `h9`'s type (produced by `soundness_append9` from
`main`'s body) and the same `jointLadder` application written with the proof's
`set`-defined abbreviations.

Bisection results (each a separate `lake env lean` run):

| Variant | Result |
|---|---|
| all six trailing hypotheses `_` | no recursion depth (only "don't know how to synthesize placeholder") |
| `hacc0 htab hT` → `_`, keep `hrb hsb h9` | recursion depth |
| `hrb hsb` → `_`, keep `hacc0 htab hT h9` | recursion depth |
| ⇒ culprit is **`h9`** | |
| `h9` → `_` (only) | recursion depth (so the check is on the `hc` slot regardless) |
| `n8` replaced by its raw `n7 + Operations.localLength (shiftedTables … n7).2` | recursion depth |
| `have h9t := h9; simp only [] at h9t` | recursion depth at the `simp` line |

So the failure is not the target, not `n8`, and not any of the other five
hypotheses: it is the comparison of the two `jointLadder` applications itself.
`set`-defined abbreviations (`hxE`, `hyE`, `n3`, `n6`, `n7`, `n8`) are transparent
local definitions, so `isDefEq` unfolds them; somewhere in that unfolding the
255-step `foldlRange` inside `jointLadder`'s body is reached and the recursion
budget is exceeded.

## Proposed fix (next round)

Seal `jointLadder`'s output the same way `fixedBase`'s is sealed, so that
`(jointLadder acc0 tables rb sb target n).2` is a stuck term:

```lean
@[irreducible] def jointLadderOps (acc0 : Pt) (tables : Tables)
    (rb sb : Vector E 256) (target : Pt) (n : Nat) : Operations Fp :=
  (jointLadder acc0 tables rb sb target n).2
```

with `jointLadder`'s body returning `(target', jointLadderOps acc0 tables rb sb target n)`
and `jointLadderOps_eq` giving the defining equation. Then the defeq check on `h9`
compares two stuck `jointLadderOps …` applications, which is cheap, and
`jointLadder_spec` unfolds the seal once via `jointLadderOps_eq` where it actually
analyses the 255-step fold.

The same treatment should be applied to `shiftedTables` (`shiftedTablesOut`), since
`(shiftedTables … n7).1` is likewise expensive to whnf (confirmed: introducing
`have htb : Tables := (shiftedTables … n7).1` and passing `htb` produced
`Application type mismatch` + `maximum recursion depth`).

## Next milestone

M5-1 (`main_soundness`) with the `jointLadderOps` / `shiftedTablesOut` seals, then
M5-2 (phase-level completeness lemmas, `main_complete_with_seed`,
`main_completeness`, `main_accepts_iff_standard`).
