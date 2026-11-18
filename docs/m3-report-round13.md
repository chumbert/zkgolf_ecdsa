# M3 round 13 report — item (e3) fixed-base phase semantics

## Timing
- before = 1795028733
- after  = 1795031290
- elapsed_seconds = 2557

## What was proved (new in `StandardECDSA/Phases/FixedBaseSemantics.lean`)

Group-level infrastructure for the fixed-base phase (plan §5):

- `toAffineLift_add`, `toAffineLift_zero` — additivity of the
  projective-to-affine map (`WeierstrassCurve.Projective.Point.toAffineLift_add`).
- `digitOf`, `digitOf_eq` — the window digit `d_i = eBit[2i] + 2·eBit[2i+1]`
  read off the environment.
- `winSum`, `winSum_succ` — the prefix window sum
  `Σ_{i<k} (4 + d_i)·4^i`.
- `digestNat` — the digest integer `E = leNat eBit` (opaque, to keep
  `leNat` out of goal statements).
- `winSum_128` — **`winSum env eb 128 = shiftNat + digestNat env eb`**, i.e. the
  128 window constants sum to the shift `S` plus the digest `E`.
- `fbMux`, `fixedBaseBody_eq` — the per-window constant mux, and the
  `>>=`-normal form of one window.
- `fbInv` — the plan §5 prefix invariant
  `ep_k = H - S + [winSum k]G`.
- `fin_foldl_inv` — generic invariant induction for `Fin.foldl`.
- `foldlAcc_eq` — `Circuit.FoldlM.foldlAcc` at window `k` equals the
  corresponding `Fin.foldl` prefix.
- `fbStep` — **one window preserves `fbInv`**: from the mux row, the
  `muxConst4W_tablePt` group semantics, `affAdd_sound` and the prefix
  invariant at `k`, derive the invariant at `k+1`.

## What remains for (e3)

`fixedBase_spec` (the final 128-step composition) is **not** proved. The
obstruction is a hard elaboration/`whnf` blow-up, not a mathematical gap:

- `soundness_bind env (affAdd h (cst shiftX, cst (-shiftY))) (fun ep0 => foldlRange …) n hc`
  times out at `whnf` (200000 heartbeats) on the defeq check
  `(fixedBase h eb).operations n ≡ ((affAdd …) >>= f).operations n`.
- The `simp only [fixedBase, Circuit.operations, Circuit.localLength, …] at hc`
  alternative also times out at `whnf` on the same term.
- `Operations.forAllNoOffset_append.mp h` (with `h` obtained by
  `simp only [fixedBase] at h`) times out at `whnf` as well.
- `set_option maxRecDepth 10000` does not help; the failure is a heartbeat
  timeout in `whnf`, not recursion depth.

`fixedBase_spec` was therefore removed from the file so that the module stays
`sorry`-free and green. All of its ingredients (`fbStep`, `winSum_128`,
`foldlAcc_eq`, `fin_foldl_inv`, `toAffineLift_add`) are proved and available.

## Checks

- `lake build` → `Build completed successfully (17893 jobs)`
- `lake build StandardECDSA.Main` → `Build completed successfully (9013 jobs)`
- `grep -rn "sorry" StandardECDSA/` → exit 1 (zero hits)
- `lake exe standardEcdsaCheck --count-only` → `allocations=4628 rows=4634 score=9262`

## Files changed

```
 M StandardECDSA/Phases/FixedBaseSemantics.lean
```

## Next milestone

M3 item (e4) `JointLadder.Spec`, then M4.
