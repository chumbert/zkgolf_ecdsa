/-
# Joint ladder phase

Ported from the pinned `circuit_baseline` revision
(`3a1bd20749ae0b6400a158651dba64a2c5fc58ff`), `Baseline/Projected/Offset.lean`.

The ladder consumes the scalar bits most-significant first (`index = 255 - j`)
and alternates the offset sign: `σ_j = -1` for even `j`, `+1` for odd `j`.
Before iteration `j`:

```text
C_0 = O
C_(j+1) = [2]C_j + T_j
T_j = [rBit[255-j]]Q + [tBit[255-j]]R
acc_j = C_j + [σ_j]H
selected_j = T_j - [3σ_j]H
acc_(j+1) = C_(j+1) - [σ_j]H
```

After 256 steps the represented point is `[r]Q + [t]R - H`.  The final step uses
`elmTo` to constrain the last output directly to `-ep`, giving exactly
`[E]G + [r]Q + [t]R = O` after cancelling `H`.

Cost: 255 × (`mux4` 6/6 + `elm` 6/6) + (`mux4` 6/6 + `elmTo` 4/6)
= 3,070 allocations and 3,072 rows.

Task T15.
-/

import StandardECDSA.Gadgets.ELM
import StandardECDSA.Gadgets.Select
import StandardECDSA.Phases.ShiftedTables

namespace StandardECDSA.Phases

open StandardECDSA.Gadgets

/-- The joint ladder.  `acc0` is the initial accumulator `-H`; `rb`/`sb` hold the
`r` and `t = n - s` bits least significant first; `target` is `-ep`. -/
def jointLadder (acc0 : Pt) (tables : Tables) (rb sb : Array E) (target : Pt) : C Unit := do
  let mut acc := acc0
  for j in [0:256] do
    let i := 255 - j
    let tab := if j % 2 == 0 then tables.plus else tables.minus
    let t ← mux4 (rb.getD i (cst 0)) (sb.getD i (cst 0))
      (tab.getD 0 acc0) (tab.getD 1 acc0) (tab.getD 2 acc0) (tab.getD 3 acc0)
    if j == 255 then
      elmTo acc t target
    else
      acc ← elm acc t

end StandardECDSA.Phases
