# Projected circuit: witness-generation exceptions catalogue

The honest prover for `Solution.Projected.main` allocates every auxiliary wire,
so witness generation performs divisions (`.inv` hints and `nonzero` inverses)
that can fail for exceptional choices of the offset point `H = c•G`. This file
catalogues those conditions; `Solution.Projected.Math.OffsetGood` (M3) proves a
`c` exists avoiding all of them simultaneously.

## Where divisions occur

1. `nonzero x` (3 uses): `pkX`, `r`, `n − s`. These depend only on the public
   inputs, not on `H`; they are discharged by the soundness-side constraints
   themselves (`x * inv = 1` forces `x ≠ 0`).
2. `affAdd p q` (fixed-base chain, offsets): one `nonzero (q.x − p.x)`.
3. `affDouble h`: one `.inv (2 * h.y)`.
4. `elmCore p q` (ladder): `nonzero (q.x − p.x)` and `.inv (p.x − xu)` where
   `xu` is the intermediate x of `p + q`.

## Conditions on H (with Q = pk, R = (r, ry), E = digest)

Writing the actual intermediate points, the catalogue is: for each ladder step
the selected table entry `X ∈ {O, Q, R, Q+R}` and sign `σ = ±1`,
`a•H ≠ B` for `a ∈ {±1, ±2, ±3, ±4}` and the relevant `B` among
`{O, Q, R, Q+R, 2H, 3H, …}` — approximately 1,032 conditions in total
(4 per ladder step × 256 steps, plus the fixed-base chain and offset
constructions).

This reconciles with `m = 1039` in `Baseline/Projected/OffsetExistence.lean`:
the existence proof there counts the bad `c` values per equation
(`c•G = B/a` has at most one solution each), and 1,039 is the rounded bound
covering the catalogue plus the fixed-base window offsets.
