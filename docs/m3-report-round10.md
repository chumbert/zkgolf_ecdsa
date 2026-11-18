# M3 progress report — round 10

## Timing

- before: **not captured** (deviation; the round began immediately after the
  round-9 report without a `date -u +%s` call)
- after: **1795027498**
- elapsed_seconds: **not computable** (before-value missing).  For reference the
  last captured value was 1795026063 (round 9, before commit `5e629ac`), so the
  round-10 wall time is at least `1795027498 - 1795026063 = 1435 s`.

## What was done

### (d) Phase cost certificates — COMPLETE

`StandardECDSA/Phases/Cost.lean` (new, 105 lines):

| theorem | statement |
|---|---|
| `fixedBaseBody_cost` | `CostIs (fixedBaseBody eb tables ep i) ⟨5, 5⟩` |
| `fixedBase_cost` | `CostIs (fixedBase h eb) ⟨644, 644⟩` |
| `shiftedTables_cost` | `CostIs (shiftedTables h q r) ⟨32, 32⟩` (given `deg h.1 = 1`) |
| `jointLadderBody_cost` | `CostIs (jointLadderBody tables rb sb acc j) ⟨12, 12⟩` |
| `jointLadderFinal_cost` | `CostIs (jointLadderFinal tables rb sb acc target) ⟨10, 12⟩` |
| `jointLadder_cost` | `CostIs (jointLadder acc0 tables rb sb target) ⟨3070, 3072⟩` |

All three phase totals match the plan §3 ledger exactly: 644/644, 32/32,
3070/3072.  The `[0:128]` / `[0:256]` loops were restructured to
`Circuit.foldlRange` with explicit `ConstantLength` instances
(`fixedBaseBody_constantLength`, `jointLadderBody_constantLength`) so that
`CostIs.foldlRange` applies and the `Count` arithmetic closes by `decide`.

### Architectural fix required to keep `main` compiling

The `foldlRange` restructuring needs a `ConstantLength` instance for the loop
body, which for `muxConst4`/`mux4`/`sel` is *stuck* on `deg (eb.get k)` when the
bit vector is an opaque local.  `main` cannot supply those degree facts: in a
`do` block the offset is not nameable, so `bitVec_deg` cannot be instantiated at
the continuation's offset.

Fix (and this is exactly what plan §6 T05 asks for — "use explicit operations
whose counts do not depend on syntactic constant-folding branches in arbitrary
inputs"): new module `StandardECDSA/Gadgets/SelectW.lean` with degree-free
variants

* `selW b x0 x1` — 1 allocation / 1 row, `localLength = 1` unconditionally;
* `muxConst4W b0 b1 tab` — 1/1, `localLength = 1` unconditionally;
* `mux4W b0 b1 p0 p1 p2 p3` — 6/6, `localLength = 6` unconditionally.

Each always allocates the product wire and always emits the product row, so the
count is a literal constant.  When the selectors are wires these are
row-for-row identical to `sel`/`muxConst4`/`mux4`, so the measured cost is
unchanged.  Proved for them: `selW_localLength`, `muxConst4W_localLength`,
`mux4W_localLength`, `selW_cost`, `muxConst4W_cost`, `mux4W_cost`,
`isR1CSCirc_selW`, `isR1CSCirc_muxConst4W`, `isR1CSCirc_mux4W`.

`main` was also restructured to build the three 256-bit hint vectors with
`Circuit.mapFinRange` (`bitBody`, `bitBody_constantLength`, `bitVec`,
`bitVec_deg`) and to recompose the digest/scalar bindings with a pure
`linComb` fold.  Allocation/row count is unchanged.

`Tables` was refactored from two `Array Pt` fields to eight named `Pt` fields
(`p0 p1 p2 p3 m0 m1 m2 m3`) plus `Tables.x0 … x3` and `Tables.Wires`, so the
ladder's table selection needs no `Array.getD` default.

### (e) Phase semantic specs — PARTIAL

`StandardECDSA/Phases/Semantics.lean` (new, 191 lines):

Proved (row level, no hypotheses beyond the row equations):

| theorem | statement |
|---|---|
| `selW_eval` | the `selW` row forces `out = x0 + b·(x1 - x0)` |
| `eval_muxConst4Coord` | `muxConst4Coord` evaluates to `muxConst4Val` |
| `muxConst4W_eval` | both coordinates are the four-way interpolation |
| `mux4W_eval` | the six rows force the three-level binary selection |
| `mux4Val_bits` | at Boolean selectors `mux4Val` picks entry `b0 + 2·b1` |
| `muxConst4Val_bits` | same for `muxConst4Val` |

Stated as interfaces but **not yet proved** (see obstruction below):
`Tables.Spec`, `FixedBase.Spec`, `JointLadder.Spec`.

## Remaining obstruction for M3 item (e)

The group-level halves of the three phase specs are blocked on two
prerequisites that are *not* in the repo yet:

1. **T11 fixed-table certification.**  `Math/FixedTables.lean` only *defines*
   `fixedTables` (128·4 = 512 entries) and `fixedShift` via `mulG`/`affine`.
   There is no kernel proof that entry `(i, d)` is `[(4+d)·4^i]G`, that it is
   finite, or that it is on curve.  `FixedBase.Spec` (`ep = H + [E]G`) cannot be
   proved without it.  This is a standalone task of the size of the whole
   `Math/` directory.
2. **Circuit-to-group bridges for `affAdd`/`affDouble`/`elm`.**  `Math/AffineBridge.lean`
   supplies `affine_add_eq_group`, `affine_double_eq_group`, `elm_eq_group` as
   *generic* lemmas over `CurveParameters F`.  Applying them to the actual rows
   requires the `affAddMain_soundness` / `elmMain_soundness` bundling of
   `Gadgets/Semantics3.lean` to be composed with the phase loops, plus the
   `GoodOffset` distinct-x hypotheses of `Math/OffsetConditions.lean`.

Neither is a mechanical step; both are multi-hundred-line proofs.  I did not
attempt to fake them with `True`-valued placeholders in the *proved* direction —
the three `Spec` definitions above are explicitly documented as unproved
interfaces, and no theorem claims them.

## Checks

```
$ lake build
Build completed successfully (17893 jobs).

$ lake build StandardECDSA.Main
Build completed successfully (9008 jobs).

$ grep -rn "sorry" StandardECDSA/
(no output, exit 1)

$ lake exe standardEcdsaCheck --count-only
Standard P-256 ECDSA circuit (6 fixed inputs)
allocations=4628 rows=4634 score=9262
```

Count is unchanged at the plan budget 4628/4634 = 9262.

## Files changed

```
 StandardECDSA/Gadgets/LocalLength.lean  | 136 +++++++++++++++++++++++
 StandardECDSA/Gadgets/LtExplicit.lean   |   6 +-
 StandardECDSA/Gadgets/SelectW.lean      | 166 +++++++++++++++++++++++++++
 StandardECDSA/Main.lean                 |  69 ++++++-----
 StandardECDSA/Phases/Cost.lean          | 105 ++++++++++++++++++
 StandardECDSA/Phases/FixedBase.lean     |  31 ++++--
 StandardECDSA/Phases/JointLadder.lean   |  43 +++++--
 StandardECDSA/Phases/Semantics.lean     | 191 ++++++++++++++++++++++++++++++++
 StandardECDSA/Phases/ShiftedTables.lean |  68 ++++++++++++++++++++
 9 files changed, 759 insertions(+), 56 deletions(-)
```

Commits: `37fb804` (phase cost certificates + degree-free mux variants),
`eb82859` (phase semantics).

## Next milestone I would attempt

M3 item (e) group-level phase specs, starting with the cheapest of the two
prerequisites: the `affAdd`/`affDouble` circuit-to-group bridge for
`shiftedTables` (needs only `Gadgets/Semantics3.lean`'s `affAddMain_soundness`
composed with `shiftedTables`'s eight additions, plus `negPt` transport), since
it does not depend on T11.  `FixedBase.Spec` and `JointLadder.Spec` remain
blocked on T11 and on the `elm` bridge respectively.
