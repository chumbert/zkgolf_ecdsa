# M4 report (round 11) — complete prover

**Milestone:** M4 (T03 signature equation, T14 offset candidates, T16 witness generation)

**Timing:** before = `1795043904`, after = `1795044662`, **elapsed_seconds = 758**

## What was proved

### M4a — T03 `Math/SignatureEquation.lean` (closed)

The missing ingredient was the finiteness characterisation of a projective
point.  Proved from the vendored `X_eq_zero_of_Z_eq_zero` /
`Y_ne_zero_of_Z_eq_zero` lemmas, **without** expanding the RCB `addZ`
polynomial:

| theorem | statement |
|---|---|
| `Z_eq_zero_iff_equiv_infinity` | `P.IsOnCurve params → (P.Z = 0 ↔ ProjectiveEquiv P infinityPoint)` |
| `ProjectiveEquiv.Z_eq_zero_iff` | `ProjectiveEquiv P Q → (P.Z = 0 ↔ Q.Z = 0)` |
| `toMathlibPoint_proof_irrel` | `toMathlibPoint` is independent of the on-curve proof |
| `affinePt` / `affinePt_X` / `affinePt_Y` | the affine point of a finite projective point |
| `projectiveEquiv_affinePt` | `P.Z ≠ 0 → ProjectiveEquiv P (affinePt P).toProjective` |
| `affinePt_isOnCurve` | `P.IsOnCurve → P.Z ≠ 0 → (affinePt P).IsOnCurve` |
| `addE3_toMathlib` | the Mathlib image of a three-term `addE` chain |
| `stdV` / `sigW` / `Qpt` | the two verification points and the public-key image |
| `stdV_on_curve` / `sigW_on_curve` | on-curve facts |
| `stdV_toMathlib` / `sigW_toMathlib` | their Mathlib-group images |
| `standard_core_iff` | the shared-prefix core equivalence |
| **`standard_iff_signaturePoint`** | `standardVerify … ↔ signaturePointVerify …` |

`x_mod_order_iff_lift` was already proved in the previous round.

### M4b — T16 `Witness/Generate.lean` + `Witness/Correctness.lean` (new)

`Witness/Generate.lean` (executable generator):

* `digestOf lo hi = lo.val + 2^128 * hi.val`
* `bitOf m i = (m / 2^i) % 2`, `bitsOf m : Fin 256 → K`
* `overflowOf rx r = if rx < n then 0 else 1`
* `offsetPt k = [k+1]G` (vendored projective representation)
* **`generateSeed pkX pkY digestLo digestHi r s fam hm : Seed`** — the full
  772-cell seed: `ry` from `V = stdV Q r s E`, `hx/hy` from the selected
  offset, `overflow`, and the three 256-bit vectors.
* `generateSeed_index_lt`, `generateSeed_offsetPt_Z_ne_zero`,
  `generateSeed_offsetPt_on_curve`, `generateSeed_offsetPt_toMathlib`

`Witness/Correctness.lean`:

| theorem | statement |
|---|---|
| `bitOf_lt_two`, `val_bitsOf` | bit extraction is canonical |
| `leNat_succ`, `mod_two_pow_succ` | the `2^(k+1)` remainder split |
| **`leNat_bitOf`** | `leNat (bitOf m) = m % 2^k` |
| `leNat_bitsOf_val` | `leNat (bitsOf m) = m % 2^256` |
| `leNat_low_half` / `leNat_high_half` | the 128-bit limb decompositions |
| `overflowOf_bool`, `bitsOf_bool` | Booleanity |
| `n_lt_two_pow_256`, `p_lt_n_add_n` | numeric bounds |
| `generateSeed_overflow_val` / `_rBits` / `_tBits` / `_digestBits` | component equations |
| **`generateSeed_scalarFacts`** | `ScalarFacts (generateSeed …) E r.val (n - s.val)` |
| `generateSeed_H_onCurve` | the offset is on the curve |
| `generateSeed_goodOffset` | `GoodOffset (Seed.H sd) hH fam` |
| **`generateSeed_complete`** | `Admissible (generateSeed …) (affineX (stdV …)) E r.val (n-s.val) hH fam` |
| `generateSeed_R_eq` | `Seed.R sd rx = affinePt (stdV …)` |
| `generateSeed_R_onCurve` | `R` is on the curve for standard-valid input |
| `generateSeed_R_x` | `R.X.val % n = r.val` |
| `overflow_split` | pure arithmetic: `x % n = r → x = r + n·overflowOf x r` |
| **`generateSeed_overflow`** | `val(x(V)) = r + n·overflow` |

`generateSeed_complete` takes the two canonical-limb hypotheses
`digestLo.val < 2^128` and `digestHi.val < 2^128` — exactly the constraints the
circuit enforces through its 128 Boolean digest bits.  No
constraint-satisfaction premise appears anywhere: `Admissible` is a predicate on
group points and naturals only.

## Remaining sorries

```
$ grep -rn "sorry" StandardECDSA/
$ echo exit=$?
exit=1
```

Zero hits.

## Build errors

None.

```
$ lake build StandardECDSA.Main
Build completed successfully (9019 jobs).
$ lake build
Build completed successfully (17893 jobs).
```

(The two `sorry` warnings in `lake build` are the pre-existing
`Challenge/Instances/ECDSA_P256_Digest/Challenge.lean` stubs, untouched by this
milestone.)

## Checks

```
$ lake exe standardEcdsaCheck --count-only
Standard P-256 ECDSA circuit (6 fixed inputs)
allocations=4628 rows=4634 score=9262

$ python3 scripts/check_axioms.py
Tests/Axioms.lean: 26 roots passed the permitted-axiom audit
```

`#print axioms` on the new roots:

```
standard_iff_signaturePoint : [propext, Classical.choice, Quot.sound]
x_mod_order_iff_lift        : [propext, Classical.choice, Quot.sound]
exists_goodOffset           : [propext, Classical.choice, Quot.sound]
findGoodOffset_spec         : [propext, Classical.choice, Quot.sound]
generateSeed_complete       : [propext, Classical.choice, Quot.sound]
generateSeed_R_onCurve      : [propext, Classical.choice, Quot.sound]
generateSeed_R_x            : [propext, Classical.choice, Quot.sound]
generateSeed_overflow       : [propext, Classical.choice, Quot.sound]
leNat_bitOf                 : [propext, Classical.choice, Quot.sound]
```

## Files changed

```
 M StandardECDSA/Main.lean
 M StandardECDSA/Math/SignatureEquation.lean
?? StandardECDSA/Witness/Correctness.lean
?? StandardECDSA/Witness/Generate.lean
```

## Notes / deviations

* `maxHeartbeats` was **not** changed.  Two `whnf` timeouts were resolved by
  restructuring rather than by raising limits:
  - `standard_core_iff` was rewritten with small helper definitions
    (`stdV`, `sigW`, `Qpt`) so no goal ever contains the unfolded RCB formula;
  - `generateSeed_overflow` was factored into the pure-arithmetic lemma
    `overflow_split` plus a one-line application, so the big `stdV` term is
    never repeated inside a tactic block.
* `stdV`/`sigW` use `FixedTables.mulG` (definitionally equal to
  `StandardECDSA.mulG`) so that `rw [FixedTables.mulG_toMathlib]` matches
  syntactically; `standard_iff_signaturePoint` still applies to the
  `standardVerify`/`signaturePointVerify` predicates unchanged.

## Next milestone

M5 (T17 `Main.lean` assembly: `main_soundness`, `main_complete_with_seed`,
`main_completeness`, `main_accepts_iff_standard` over the actual circuit
`main`).
