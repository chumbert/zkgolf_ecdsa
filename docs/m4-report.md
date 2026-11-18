# M4 report — round 16 (T03, T14, T16)

## Timing

| | value |
|---|---|
| before (`date -u +%s`) | **1795043012** |
| after (`date -u +%s`) | **1795043850** |
| elapsed_seconds | **838** |

## Milestone status: **M4 PARTIAL**

| task | file | state |
|---|---|---|
| T14 | `StandardECDSA/Math/OffsetCandidates.lean` | **COMPLETE** |
| T03 | `StandardECDSA/Math/SignatureEquation.lean` | **group-level core COMPLETE**; concrete `standard_iff_signaturePoint` **BLOCKED** (see below) |
| T16 | `StandardECDSA/Witness/Generate.lean`, `Witness/Correctness.lean` | **NOT STARTED** |

## What was proved

### T14 — `StandardECDSA/Math/OffsetCandidates.lean` (new, complete)

* `offsetCandidate (k : Fin 1040) = [k+1]G` — the 1,040 concrete candidates.
* `thousand_forty_lt_n : 1040 < n`.
* **`offsetCandidate_injective`** — the candidates are pairwise distinct.  Proof:
  from `[p+1]G = [q+1]G` with `p ≤ q` derive `[q-p]G = 0`, hence
  `addOrderOf Gpt = n ∣ q - p`, hence `q - p = 0` because `q - p < 1040 < n`.
* **`exists_goodOffset`** — for any `BadFamily` with `fam.m < 1040`,
  `∃ k : Fin 1040, fam.Avoids (offsetCandidate k)`, by instantiating
  `exists_avoiding_of_injective` (`Math/OffsetConditions.lean`) with the
  injective candidate map.
* `exists_goodOffset_nat` — the same as a bounded search over `k < 1040`.
* `findGoodOffset` / `findGoodOffset_spec` / `findGoodOffset_lt` /
  `findGoodOffset_ne_zero` — the search result, its specification, its index
  bound, and its finiteness (`≠ 0`).

No assumption that `H = G` or `H = [2]G` works: the theorem quantifies over all
1,040 candidates and only uses `m < 1040`.

### T03 — `StandardECDSA/Math/SignatureEquation.lean` (new, group-level core)

Group-level scalar arithmetic on `Grp := (params.toMathlib).toProjective.Point`:

* `nsub_nsmul` — `[n - s]P = -[s]P` for `s ≤ n`.
* `nsmul_mod_congr` — `a ≡ b (mod n) → [a]P = [b]P`.
* `nsmul_add'`, `nsmul_sub'`, `nsmul_neg'` — `Nat`-scalar distributivity,
  proved by induction because the group's `SMul ℕ` instance is `NSMul.toSMul`
  rather than a `DistribSMul`, so `smul_add`/`smul_sub` do not apply.
* `mul_inv_mod_left` — `s·(E·w) ≡ E (mod n)` when `s·w ≡ 1 (mod n)`.

The signature equation:

* **`signature_equation_iff`** — with `0 < s < n`, `w = s⁻¹ mod n`,
  `u₁ = E·w mod n`, `u₂ = r·w mod n`, `t = n - s`:
  `[E]G + [r]Q + [t]R = 0 ↔ R = [u₁]G + [u₂]Q`.
  Forward: `[s]V = [E]G + [r]Q` from `s·u₁ ≡ E`, `s·u₂ ≡ r`; `[t]R = -[s]R`;
  the circuit equation gives `[t]R = -([E]G + [r]Q)`; so `[s]R = [s]V`, and
  `[s]` is injective (`nsmul_injective_of_lt`).  Backward: `[t]R = -[s]R =
  -([E]G + [r]Q)`, so the sum vanishes.

The `x`-coordinate lift:

* **`x_mod_order_iff_lift`** — for `0 < r < n`, Boolean `overflow`, and
  `r + n·overflow < p`: `val((r + n·overflow : K)) = r + n·overflow` and
  `val(...) % n = r`.  This is the arithmetic content of the circuit's
  `rx = r + n·overflow` branch.

Bridges to the Mathlib group (all transported from the vendored
kernel-checked `ECBridge` lemmas):

* `s_mul_invModN` — `s · (s⁻¹ mod n) ≡ 1 (mod n)` for `0 < s < n`.
* `toProjective_on_curve` — the projective lift of an affine on-curve point is
  on the curve.
* `mulP_on_curve`, `mulP_toMathlib` — `mulP k P` is on the curve and equals
  `[k]P` in the Mathlib group.
* `addE_toMathlib` — `addE` is the group sum.
* `projectiveEquiv_iff_toMathlib` — `ProjectiveEquiv` is group equality.
* `infinity_toMathlib` — `infinityPoint` is `0`.
* `affineX_eq_of_projectiveEquiv`, `affineY_eq_of_projectiveEquiv` — the affine
  coordinates of a projectively equivalent point.

## Exact obstruction for the concrete `standard_iff_signaturePoint`

`standardVerify`'s finiteness condition is `¬ ProjectiveEquiv V infinityPoint`
where `V = addE (mulG u₁) (mulP u₂ Q.toProjective) params`.  To build the affine
witness `R` for `signaturePointVerify` one takes
`R := ⟨affineX V, V.Y * V.Z⁻¹⟩`, which requires `V.Z ≠ 0`.

`addE_on_curve` gives `V.IsOnCurve params`, i.e.
`V.SatisfiesCurveEquation params ∧ V ≠ 0`.  **`V ≠ 0` does not imply
`V.Z ≠ 0`**: the point `⟨0, 1, 0⟩` satisfies the curve equation and is not
`0 = ⟨0,0,0⟩`, yet has `Z = 0` and is *not* projectively equivalent to
`infinityPoint`.  So `¬ ProjectiveEquiv V infinityPoint` cannot be converted
into `V.Z ≠ 0` with the lemmas currently available.

The missing ingredient is a characterisation of `addE`'s `Z`-coordinate:

```text
(addE P Q params).Z = 0 ↔ addE P Q params = infinityPoint
```

This is true for the RCB complete formula on a prime-order curve, but it is not
proved in the vendored `ECBridge` sources and would have to be added (it is a
statement about the explicit `addZ` polynomial).  With it, the forward direction
closes by `affineX_eq_of_projectiveEquiv` + `signature_equation_iff`; the
backward direction is immediate (`R` is given, `V = R` by
`signature_equation_iff`, and `affineX_eq_of_projectiveEquiv` transfers the
`x`-condition).

## Checks (observed)

```
$ lake build StandardECDSA.Main
Build completed successfully (9017 jobs)

$ lake build StandardECDSA.Math.SignatureEquation
Build completed successfully

$ lake build StandardECDSA.Math.OffsetCandidates
Build completed successfully

$ lake exe standardEcdsaCheck --count-only
Standard P-256 ECDSA circuit (6 fixed inputs)
allocations=4628 rows=4634 score=9262

$ grep -rn "sorry" StandardECDSA/
(no output, exit 1)

$ python3 scripts/check_axioms.py
Tests/Axioms.lean: 26 roots passed the permitted-axiom audit

$ #print axioms signature_equation_iff / x_mod_order_iff_lift /
  # exists_goodOffset / offsetCandidate_injective
all: [propext, Classical.choice, Quot.sound]
```

## Remaining sorries

```
$ grep -rn "sorry" StandardECDSA/
$ echo $?
1
```

Zero hits.

## Build errors

None.

## Files changed

```
 M StandardECDSA/Main.lean                        |   2 +
?? StandardECDSA/Math/OffsetCandidates.lean      | 137 (new)
?? StandardECDSA/Math/SignatureEquation.lean     | 253 (new)
```

## Next milestone

**M4 continuation**, in this order:

1. Add the `addE`-`Z` characterisation
   `(addE P Q params).Z = 0 ↔ addE P Q params = infinityPoint` (from the
   explicit `addZ` polynomial in `ECBridge`), then close
   `standard_iff_signaturePoint` using `signature_equation_iff`,
   `affineX_eq_of_projectiveEquiv` and `s_mul_invModN`.
2. T16 `Witness/Generate.lean` + `Witness/Correctness.lean`:
   `R = V` for valid inputs (from item 1), seed extraction (`ry`, `hx`/`hy`,
   canonical `overflow`, `r`/`t`/digest bits), the bounded `H` search via
   `findGoodOffset`, `generateSeed_complete`, and explicit malformed-input
   handling.

Then M5 (T17 `Main.lean` assembly) and M6 (T18/T19/T20).
