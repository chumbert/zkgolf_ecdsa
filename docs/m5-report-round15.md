# M5 report (T17 whole-circuit assembly) — round 15

Timing: before = `1795052773`, after = `1795054033`, elapsed_seconds = **1260**.

## Status

M5 is **not** complete, but **M5-1 (`main_soundness`) is now fully proved** and
M5-2 (phase-level completeness) is half done.

## M5-1 — `main_soundness` PROVED

`StandardECDSA/Main.lean` now contains

```lean
theorem main_soundness (inp : Var Input Fp) (env : Environment Fp) (n : Nat)
    (hc : ConstraintsHold.Soundness env ((main inp).operations n)) :
    standardVerify (Expression.eval env inp.pkX) (Expression.eval env inp.pkY)
      (Expression.eval env inp.digestLo) (Expression.eval env inp.digestHi)
      (Expression.eval env inp.r) (Expression.eval env inp.s)
```

**Unconditional over every satisfying assignment of all auxiliary wires** — no
good-hint assumption, no assumption on `Q` beyond what the circuit checks.

`#print axioms StandardECDSA.main_soundness` →
`[propext, Classical.choice, Quot.sound]`.

### The `jointLadderOps` seal (the unblock)

`StandardECDSA/Phases/JointLadder.lean`:

```lean
@[irreducible] def jointLadderOps (acc0 : Pt) (tables : Tables) (rb sb : Vector E 256)
    (target : Pt) (n : Nat) : Operations Fp := <the 255-step fold ++ final elmTo>
theorem jointLadderOps_eq : jointLadderOps acc0 tables rb sb target n = <body> := by
  unfold jointLadderOps; rfl
```

`jointLadder`'s body now returns `(e.1, jointLadderOps acc0 tables rb sb target n)`,
so the `h9` defeq check in `main_soundness` compares two *stuck* applications
instead of unfolding the 255-step `Fin.foldl`. `jointLadder_ops` was re-proved as
`show jointLadderOps … = _; rw [jointLadderOps_eq]; simp only [Circuit.operations,
Circuit.output, jointLadderFold_localLength]`.

`shiftedTablesOut` was **not** needed: both sides of the `tables` argument are
syntactically identical, so no `whnf` is required there.

### Supporting lemmas added to `Main.lean`

`toAffineLift_nsmul`, `toAffineLift_toMathlibPoint`, `main_group_algebra`
(`E • Gpt + r • Qpt + t • Rpt = 0` from `ep = H + [E]G`, `target = r•Q + t•R - H`,
`target = -ep`), `shiftedTables_out`, `tables_x0_fst/snd … tables_x3_fst/snd`,
`sigma_eq`, `shiftedTables_htab`, `prefVal_rev_nat`, `seed_hx_deg`,
`affDouble_hy`, `eval_r_plus_overflow`.

### Three `rw` failures fixed this round

1. `rw [← hrv] at hle` → `rw [hrv] at hle` (`hle` was already in `leNat` form).
2. `rw [projectiveEquiv_iff_toMathlib …]` did not fire because the goal's point is
   the *unfolded* `addE (addE (mulG E) …) …` while `sigW` uses
   `FixedTables.mulG`; `rw` matches at `reducible` transparency and cannot unfold
   the two `def`s. Fixed by `refine (projectiveEquiv_iff_toMathlib (sigW …) infinityPoint ?_ _).mpr ?_`
   (explicit `P`, so unification at default transparency does the work).
3. `rw [eval_add', eval_sc', eval_cst, nFp]` → `simp only […]` (`rw` does not
   unfold the regular `def` `nFp`).

## M5-2 — phase-level completeness (partial)

New in `Main.lean` (all proved, no `sorry`):

| Lemma | Statement |
|---|---|
| `eval_pm_var` | `eval env (pm a (var ⟨i⟩)) = eval env a * env.get i` |
| `getD_eq_default` | `¬ k < 256 → v.getD k (cst 0) = cst 0` |
| `lit_nFp` | `(115792089210356248762697446949407573529996955224135760342422259061068512044369 : Fp) = (Challenge.Specs.ECDSAP256.n : Fp)` |
| `seedPhase_complete` | `ULWC n (seedPhase inp n).2 → overflow Boolean → ConstraintsHold.Completeness env (seedPhase inp n).2` |
| `nonzeroPhase_complete` | `… → eval r ≠ 0 → eval (n - s) ≠ 0 → Completeness (nonzeroPhase inp n).2` |
| `isOnCurve_complete` | `… → y² = x³ + pa·x + pb → Completeness (isOnCurve x y).operations n` |
| `curvePhase_complete` | three curve equations → `Completeness (curvePhase inp s n).2` |
| `bitBody_complete` | Boolean hint → `Completeness (bitBody base stride i).operations n` |
| `bitVec_complete` | 256 Boolean bits → `Completeness (bitVec base stride).operations n` |
| `bitsPhase_complete` | three Boolean bit vectors → `Completeness (bitsPhase n).2` |
| `bindPhase_complete` | four `linComb` recompositions → `Completeness (bindPhase inp b n).2` |
| `assertLtOrderOf_complete` | `ltLoop_complete` lifted to `assertLtOrderOf` |
| `assertLtOrderGuardedOf_complete` | `ltLoopGuarded_complete` lifted to `assertLtOrderGuardedOf` |
| `cmpPhase_complete` | three comparator bounds → `Completeness (cmpPhase b overflow n).2` |
| `affAdd_complete` | `eval q.1 - eval p.1 ≠ 0 → Completeness (affAdd p q).operations n` |
| `affDouble_complete` | `eval p.2 ≠ 0 → Completeness (affDouble p).operations n` |

All are stated over `ProverEnvironment` with `UsesLocalWitnessesCompleteness`
(the Clean completeness notion, matching `Baseline/ECDSA_P256_Digest/Completeness`),
and compose the existing gadget-level `mat_complete`, `assertZeroLazy_complete`,
`ltLoop_complete`, `ltLoopGuarded_complete`.

### Still missing for M5-2

- `fixedBase_complete`, `shiftedTables_complete`, `jointLadder_complete`
  (128- and 255-step loop completeness; needs the same anti-`whnf` discipline as
  the soundness side).  `affAdd_complete` / `affDouble_complete` are the leaf
  bricks for these; `shiftedTables_complete` needs the eight distinct-`x`
  denominators, which should be packaged through `Math/OffsetConditions.GoodOffset`
  rather than written out as eight explicit hypotheses (the explicit form is
  ~60 lines of nested `Operations.localLength` terms).
- `main_complete_with_seed`, `main_completeness`, `main_accepts_iff_standard`.
- The `ConstraintsHold.Completeness → ConstraintsHold.Soundness` bridge needed by
  the forward direction of `main_accepts_iff_standard` (our circuit has no
  subcircuits and no lookups, so `constraintsHold_soundness_iff_forall_mem` plus
  `ops.subcircuits = []` should suffice).

## Checks observed

```
lake build StandardECDSA.Main      -> Build completed successfully (9020 jobs)
grep -rn "sorry" StandardECDSA/    -> exit 1 (zero hits)
lake exe standardEcdsaCheck --count-only
  -> allocations=4628 rows=4634 score=9262
#print axioms StandardECDSA.main_soundness
  -> [propext, Classical.choice, Quot.sound]
```

## Files changed

```
M StandardECDSA/Main.lean
M StandardECDSA/Phases/JointLadder.lean
```
