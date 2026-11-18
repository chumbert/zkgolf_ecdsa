# M3 report — round 11 (item (e1): shiftedTables group spec)

## Timing

- before: `1795027552`
- after: `1795028623`
- elapsed_seconds: **1071**

## What was proved

New file `StandardECDSA/Phases/TableSemantics.lean` (382 lines, no `sorry`):

### Offset-generic row-level soundness (the blocker from round 10)

| Theorem | Statement |
|---|---|
| `eval_sc` | `Expression.eval env (sc c e) = c * Expression.eval env e` |
| `affAdd_sound` | the four rows of `affAdd p q` at offset `n` give `some (env.get (n+2)) (env.get (n+3)) hR = P + Q` |
| `affDouble_sound` | the four rows of `affDouble p` at offset `n` (given `deg p.1 = 1`) give `some (env.get (n+2)) (env.get (n+3)) hR = 2 • P` |

`affDouble_sound` was the round-10 failure (`maximum recursion depth has been
reached`).  Root cause found: the goal's first component is
`(2 * eval p.2) * l = 3 * (eval p.1 * eval p.1) + pa`, while the row is
`(2 * eval p.2) * l - 3 * (eval p.1 * eval p.1) - pa = 0`, i.e. `(A - B) - C = 0`.
`sub_eq_zero.mp` therefore yields `A - B = C`, **not** `A = B + C`; the mismatch
made the elaborator diverge while unifying the (large) `Fp` expression.  Fix:
state the intermediate as `A - B = C` and convert with `eq_add_of_sub_eq` +
`add_comm`.  No `maxHeartbeats`/`maxRecDepth` change was needed.

### Composition and transport infrastructure

| Theorem | Statement |
|---|---|
| `soundness_bind` | `ConstraintsHold.Soundness env ((c >>= f).operations n)` splits into the constraints of `c` and of `f (c.output n)` at `n + c.localLength n` |
| `affAdd_localLength'`, `affDouble_localLength'` | projection-level `Operations.localLength … = 4` (the shape that appears inside `do`-block offsets) |
| `negY_eq_neg` | `Affine.negY Wp x y = -y` (P-256 has `a₁ = a₃ = 0`) |
| `negPt_ns` | `NS x y → NS x (-y)` |
| `negPt_group` | `some x (-y) _ = - some x y _` |
| `affAdd_output`, `affDouble_output` | output-coordinate equations for the two gadgets |
| `affAdd_out_fst/snd`, `affDouble_out_fst/snd` | `Expression.eval env ((affAdd p q n).1.1) = env.get (n+2)` etc. |
| `ns_congr`, `some_congr`, `negPt_some_congr` | coordinate congruence at the `NS` / `Affine.Point.some` level |
| `eval_neg'` | `Expression.eval env (-a) = -Expression.eval env a` (local copy; Clean's `eval_neg` lives in a `section`, not a namespace, so it is not reachable as `Expression.eval_neg`) |
| `nsmul_two_add` | `2 • P + P = 3 • P` |

### The phase spec (item (e1))

```lean
theorem shiftedTables_spec (env : Environment Fp) (h q r : Pt) (n : ℕ) (hdeg : deg h.1 = 1)
    (hH : NS (Expression.eval env h.1) (Expression.eval env h.2))
    (hQ : NS (Expression.eval env q.1) (Expression.eval env q.2))
    (hR : NS (Expression.eval env r.1) (Expression.eval env r.2))
    (hy : 2 * Expression.eval env h.2 ≠ 0)
    (hdx1 : Expression.eval env h.1 - env.get (n + 2) ≠ 0)
    (hdx2 : Expression.eval env q.1 - env.get (n + 6) ≠ 0)
    (hdx3 : Expression.eval env r.1 - env.get (n + 6) ≠ 0)
    (hdx4 : Expression.eval env r.1 - env.get (n + 10) ≠ 0)
    (hdx5 : Expression.eval env r.1 - env.get (n + 22) ≠ 0)
    (hc : ConstraintsHold.Soundness env ((shiftedTables h q r).operations n)) :
    ∃ (h0 : NS (env.get (n + 6)) (env.get (n + 7))) … (h7 : NS (env.get (n + 30)) (env.get (n + 31))),
      some (env.get (n + 6))  (env.get (n + 7))  h0 = 3 • H ∧
      some (env.get (n + 10)) (env.get (n + 11)) h1 = 3 • H + Q ∧
      some (env.get (n + 14)) (env.get (n + 15)) h2 = 3 • H + R ∧
      some (env.get (n + 18)) (env.get (n + 19)) h3 = 3 • H + Q + R ∧
      some (env.get (n + 6))  (-(env.get (n + 7))) h4 = -(3 • H) ∧
      some (env.get (n + 22)) (env.get (n + 23)) h5 = -(3 • H) + Q ∧
      some (env.get (n + 26)) (env.get (n + 27)) h6 = -(3 • H) + R ∧
      some (env.get (n + 30)) (env.get (n + 31)) h7 = -(3 • H) + Q + R
```

where `H = some (eval h.1) (eval h.2) hH`, `Q`, `R` likewise.  Proved by
peeling the eight `do`-block steps with `soundness_bind` (offsets `n`, `n+4`,
…, `n+28`) and applying `affDouble_sound` once and `affAdd_sound` seven times,
with `negPt_group` for the `-3H` table.

**Plan §3A compliance.**  The construction never asks for affine coordinates of
the unshifted `Q + R`: the only additions are `2H+H`, `3H+Q`, `3H+R`,
`(3H+Q)+R`, `(-3H)+Q`, `(-3H)+R`, `((-3H)+Q)+R`.  Hence it is available when
`Q + R = O` or `Q = R`; those cases only make some of the five distinct-`x`
conditions unsatisfiable, which is exactly what the global offset theorem
(T13/T14) must avoid.  The five conditions are the complete set for the eight
additions (`hdx2`/`hdx3` are each used twice).

**Table order.**  `Tables.sel t j b0 b1` (new, `Phases/ShiftedTables.lean`)
selects entry `b0 + 2·b1` of the table used at step `j` (`+` table for even
`j`, `-` table for odd `j`), i.e. exactly `rBit + 2·tBit`.  The eight group
values above are the complete input the ladder needs; the `j % 2` / `(b0,b1)`
case split is left to the ladder (item (e4)).

## Remaining sorries

```
$ grep -rn "sorry" StandardECDSA/
$ echo $?
1
```
Zero hits.

## Build errors

None.

```
$ lake build
Build completed successfully (17893 jobs)

$ lake build StandardECDSA.Main
Build completed successfully (9013 jobs)

$ lake exe standardEcdsaCheck --count-only
Standard P-256 ECDSA circuit (6 fixed inputs)
allocations=4628 rows=4634 score=9262
```

Count unchanged: **4628 / 4634 = 9262**, matching the plan budget exactly.

## Files changed

```
$ git status --short
 M StandardECDSA/Main.lean
 M StandardECDSA/Phases/ShiftedTables.lean
?? StandardECDSA/Phases/TableSemantics.lean

$ git diff --stat
 StandardECDSA/Main.lean                 |  1 +
 StandardECDSA/Phases/ShiftedTables.lean | 10 ++++++++++
 2 files changed, 11 insertions(+)
```

`StandardECDSA/Phases/TableSemantics.lean` is new (382 lines).

## M3 status after this round

| Item | Status |
|---|---|
| (1) cost certificates | ✅ closed (round 2) |
| (2) `IsR1CSCirc` per-shape lemmas | ✅ closed (round 2) |
| (3)(a) field-level `FormalAssertion` bundling | ✅ closed (round 3) |
| (3)(4) gadget soundness/completeness bundling (sel, muxConst4, affAdd, affDouble, elm, elmTo, isOnCurve, pointEquality, mux4) | ✅ closed (rounds 4–5) |
| (3)(c) comparator semantic specs | ✅ closed (round 6) |
| (d) phase cost certificates (644/644, 32/32, 3070/3072) | ✅ closed (round 6) |
| **(e1) `shiftedTables` group spec** | ✅ **closed this round** |
| (e2) T11 `Math/FixedTables.lean` kernel certification of the 128·4 entries, shift `S`, window-sum identity | ❌ **not started** |
| (e3) `FixedBase.Spec`: `ep = H + [E]G` by 128-step induction | ❌ **not started** |
| (e4) `JointLadder.Spec`: signed-offset prefix invariant, 255 steps + final `elmTo` | ❌ **not started** |

### Exact obstruction for (e2)

`Math/FixedTables.lean` currently contains only definitions (`KP`, `affine`,
`gPoint`, `mulG`, `fixedTables`, `fixedShift`) — no certification.  T11 asks for
a kernel-checked proof that each of the 512 entries is `[(4+d)·4^i]G`, finite
and on curve, plus `S = [4·Σ_{i<128}4^i]G` with affine coordinates and `S ≠ O`,
plus the window-sum/cancellation identity for every 256-bit `E`.  This needs
(a) a certified scalar-multiplication chain for `[k]G` for the 512 concrete
`k` values (or a recurrence `[4^i]G` / `[4^{i+1}]G` with `d ∈ {0,1,2,3}`), and
(b) the group-order facts from `Math/GroupOrder.lean` to make the reduction
modulo `n` sound.  `Math/GroupOrder.lean` currently exports the P-256 order
facts only as far as recorded in the M1 report; the concrete `[n]G = O`
certificate and `N = n` cardinality argument are the prerequisite.  This is the
critical-path item and it is the largest remaining piece of M3.

### Exact obstruction for (e3)

`FixedBase.Spec` needs `Math/FixedTables.lean`'s certification (e2) to know that
the 128 window constants are `[(4+d_i)·4^i]G` and that `S` is the shift.  The
128-step induction itself is straightforward once (e2) lands: the invariant
`ep_k = H - S + Σ_{i<k}[(4+d_i)·4^i]G` is preserved by `muxConst4W` +
`affAdd`, and `ep_128 = H + [E]G` follows from the window-sum identity.

### Exact obstruction for (e4)

`JointLadder.Spec` needs the `elm`/`elmTo` row-level soundness at arbitrary
offsets (the analogue of `affAdd_sound`/`affDouble_sound` proved this round) plus
the `GoodOffset` distinct-`x` hypotheses threaded through 255 steps.  The
`elm`/`elmTo` bundling exists at the `FormalCircuit` level
(`elmMain_soundness`, `elmToSpec` in `Gadgets/Semantics3.lean`), but the
offset-generic row-level form used by `jointLadderBody` is not yet derived; that
is the next concrete step after (e2)/(e3).

## Next milestone

Continue M3 with **(e2)**: T11 fixed-table certification in
`Math/FixedTables.lean`, which unblocks (e3) and is the prerequisite for the
`FixedBase` phase spec.
