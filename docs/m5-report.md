# M5 report (T17 whole-circuit assembly) — PARTIAL

Timing: before = `1795047795`, after = `1795052182`, elapsed_seconds = **4387**.

## Status

M5 is **not** complete. `main_soundness` is drafted in full but blocked by a single
elaboration problem (see "Exact obstruction"). Everything else in the repo is green.

## Landed this round (committed, builds green)

| File | Change |
|---|---|
| `StandardECDSA/Phases/TableSemantics.lean` | new theorem `shiftedTables_snd (h q r : Pt) (n : Nat) : (shiftedTables h q r n).2 = (shiftedTables h q r).operations n := rfl` — stated with opaque arguments so the `rfl` never unfolds the `do`-notation bind chain. Lets parents convert a `Soundness` hypothesis about `(shiftedTables h q r n).2` into one about `(shiftedTables h q r).operations n` without a definitional-unfolding check. |
| `StandardECDSA/Phases/LadderSemantics.lean` | `jointLadder_spec`'s constraint hypothesis simplified from the three-parameter form `(L : Operations Fp) (hc : Soundness env L) (hL : (jointLadder … n).2 = L)` to the direct form `(hc : ConstraintsHold.Soundness env ((jointLadder acc0 tables rb sb target n).2))`. The internal `hL2 : (jointLadder … n).2 = (jointLadder …).operations n := rfl` is cheap because the arguments are opaque variables. |

## Verified checks

```
lake build StandardECDSA.Main      -> Build completed successfully (9020 jobs)
grep -rn "sorry" StandardECDSA/    -> exit 1 (zero hits)
lake exe standardEcdsaCheck --count-only
  -> allocations=4628 rows=4634 score=9262
```

## What is proved in the draft of `main_soundness` (in `/tmp/s32.lean`, not yet in `Main.lean`)

All of the following compile:

- `soundness_append9` split of `hc` into the nine stage hypotheses `h1 … h9`.
- `seedPhase_sound`, `curvePhase_sound`, `nonzeroPhase_sound`, `bitsPhase_sound`,
  `bindPhase_sound`, `cmpPhase_sound` applied.
- `fixedBase_dx` + `fixedBase_spec` applied; `hEpP : some (eval pp.1) (eval pp.2) hnsEp
  = some (eval hxE) (eval hyE) hHns + toAffineLift (digestNat env eb • Gpt)`.
- `shiftedTables_hy`, `shiftedTables_dx`, `shiftedTables_htab` applied (via `h8'`
  obtained with `Eq.mp (congrArg …) (shiftedTables_snd …) h8`).
- `hacc0`, `hT`, `hneg` (the `negPt` facts for the ladder's initial accumulator and
  final target).
- `main_group_algebra` (already proved) reduces the three-term equation
  `E•G + r•Q + t•R = 0` to the affine `hEpP`/`hTgt`/`hneg` inputs.
- `x_mod_order_iff_lift` and the final `standard_iff_signaturePoint` assembly.

The **only** missing piece is the `hc` argument of `jointLadder_spec`.

## Exact obstruction

`main`'s body binds `ep := fixedBase (s.1.hx, s.1.hy) (bitsPhase n3).1.eb n6` and passes
`(ep.1.1, -ep.1.2)` as the ladder target. After `rw [main_ops] at hc` and
`soundness_append9`, the ladder hypothesis is

```
h9 : ConstraintsHold.Soundness env
       ((jointLadder (hxE, -hyE) ((shiftedTables … n7).1) rb sb
           (((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.1,
            -((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.2)) n8).2)
```

`jointLadder_spec` needs the same hypothesis with the target written `(pp.1, -pp.2)`,
where `pp` is an opaque local with `hp : (fixedBase …).output n6 = pp`. `pp` must be
opaque because `Expression.eval` is a *pattern-matching def*
(`Clean/Circuit/Expression.lean:86`), so any defeq check mentioning
`Expression.eval env ((fixedBase … n6).1.1)` unfolds `fixedBase`'s 128-step
`foldlRange` and dies.

Every route to convert `h9` fails:

1. `rw [hp1, hp2] at h9` (with `hp1 : (fixedBase … n6).1.1 = pp.1`,
   `hp2 : (fixedBase … n6).1.2 = pp.2`) — `rw` unfolds the `Soundness` def while
   abstracting, so the resulting hypothesis has the unfolded
   `…forAllNoOffset {…}` type; the subsequent defeq check against
   `Soundness env ((jointLadder … (pp.1, -pp.2) n8).2)` then whnf-unfolds
   `(jointLadder …).2` and reports
   `maximum recursion depth has been reached`.
2. `Eq.mp (congrArg (fun L => Soundness env L) hL) h9` with
   `hL : (jointLadder … (X, Y) n8).2 = L` — the `hL` argument of the spec then needs
   `(jointLadder … (pp.1, -pp.2) n8).2 = L`, whose defeq check against `hL` whnf-unfolds
   the 255-step fold: `maximum recursion depth has been reached`.
3. `Eq.mp (congrArg (fun t => Soundness env ((jointLadder … t n8).2)) htg) h9` with
   `htg : (X, Y) = (pp.1, -pp.2)` — the `Eq.mp` application itself reports
   `maximum recursion depth has been reached` (the motive's `f LHS` is compared with
   `h9`'s type, which whnf-unfolds the fold).
4. `let pp : Pt := (fixedBase …).output n6` (transparent) — then `Expression.eval env pp.1`
   unfolds `pp` and hence `fixedBase`: `maximum recursion depth has been reached`.
5. `set pp := …` — the `set` tactic itself reports
   `maximum recursion depth has been reached` at the `set` line.

Raising `maxRecDepth` (diagnostic only, not committed) converts the failure into
`(deterministic) timeout at whnf, maximum number of heartbeats (200000) has been reached`,
confirming this is a genuine 128-step unfolding, not a shallow recursion limit.

## Proposed fix (next round)

Make `(fixedBase h eb n).1` cheap to whnf by sealing the fold's output behind an
`@[irreducible]` helper, e.g. in `Phases/FixedBaseSemantics.lean`:

```lean
@[irreducible] def fixedBaseOut (h : Pt) (eb : Vector E 256) (n : Nat) : Pt :=
  (Circuit.foldlRange 128 ((affAdd h (cst shiftX, cst (-shiftY))).output n)
      (fixedBaseBody eb fixedTables) (fixedBaseBody_constantLength eb fixedTables)).output (n + 4)
```

and define `fixedBase h eb n = (fixedBaseOut h eb n, <ops>)`. Then
`(fixedBase … n6).1` whnf-reduces to the stuck term `fixedBaseOut … n6`, so
`h9`'s type becomes cheap, `hp1`/`hp2` become cheap, and `rw [hp1, hp2] at h9`
(or even a plain defeq check) succeeds. `fixedBase_spec` / `fixedBase_ops` /
`fixedBase_dx` then need `unfold fixedBaseOut` at the points where the fold is
actually analysed — a mechanical change.

The same seal should be applied to `jointLadder`'s final target if the ladder's own
`hTgt` turns out to need it.

## Next milestone

M5-1 (`main_soundness`) with the `fixedBaseOut` seal, then M5-2 (phase-level
completeness lemmas, `main_complete_with_seed`, `main_completeness`,
`main_accepts_iff_standard`).
