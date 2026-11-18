# T00 Source Manifest and Reproducibility Log

## Pinned source revisions

| Source | Revision | Description |
|---|---|---|
| Local `optimized-proofs` | `4d57ece87d9968dc5cca653c97897beadfc08a9b` | Completed 18,612-cost pointwise circuit proof; reusable arithmetic, cost, audit and validation patterns |
| `compsec-epfl/zkgolf_ecdsa`, `circuit_baseline` | `3a1bd20749ae0b6400a158651dba64a2c5fc58ff` | Measured 9,267 experiment, ELM algebra/group bridges, abstract offset-existence proof |
| Longfellow proof sources | `4fe092be7e8e9634cd3b27daf55695a3a416043e` | EC arithmetic and compatible no-two-torsion certificate |

## Reference worktree reproduction (3a1bd20)

Worktree: `/tmp/opencode/zkgolf-circuit-baseline-3a1bd20` (detached HEAD at 3a1bd20)

### Build
```
lake build projected Baseline.Projected.Audit
# Build completed successfully (17953 jobs).
```

### Executable count
```
lake exe projected --count-only
# allocations=4631 rows=4636 score=9267 R1CS violations=0
```

### Full execution
```
lake exe projected
# H search local-generator: H=2G
# vectors: 252 agree, 0 disagree (166 source accepted, 24 byte-format cases skipped)
# offset search: max H=2, sum H=168; rejected cases tested only H=G
# digest p+1 lift: original=true offset H=(some 2) field digest=1
# Q=3G,R=2G,e=1 retry: original=true, H=G failure=(some 1540), first satisfying H=(some 2)
```

### Matrix export and check
```
lake exe projected --export Baseline/Projected/generated
# exported 4636 rows, 4631 additional variables, score 9267

python3 Baseline/Projected/check_matrices.py Baseline/Projected/generated
# field_prime: 115792089210356248762697446949407573530086143415290314195533631308867097853951
# additional_allocations: 4631, rows: 4636, score: 9267
# matrix_sha256: b3b50f54f145220d7727ba112f51cd19fca0999b71db54c167e2955c0678a68c
# sample_satisfies: true, input_mutations_rejected: 5, auxiliary_mutations_rejected: 4631
```

## Main branch build

```
lake build
# Build completed successfully (17893 jobs).
```

## StandardECDSA skeleton

```
lake build StandardECDSA
# Build completed successfully (4 jobs).
```
