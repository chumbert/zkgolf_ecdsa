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
import StandardECDSA.Gadgets.LocalLength
import StandardECDSA.Gadgets.SelectW
import StandardECDSA.Gadgets.Select
import StandardECDSA.Phases.ShiftedTables

namespace StandardECDSA.Phases

open StandardECDSA.Gadgets

/-- One returning ladder step: select `T_j` from the alternating table and
combine it with `[2]C_j` via `elm`. -/
def jointLadderBody (tables : Tables) (rb sb : Vector E 256) (acc : Pt) (j : Fin 255) : C Pt := do
  let t ← mux4W (rb.get ⟨255 - j.val, by omega⟩) (sb.get ⟨255 - j.val, by omega⟩)
    (tables.x0 j.val) (tables.x1 j.val) (tables.x2 j.val) (tables.x3 j.val)
  elm acc t

/-- Every returning ladder step allocates exactly twelve wires. -/
def jointLadderBody_constantLength (tables : Tables) (rb sb : Vector E 256) :
    Circuit.ConstantLength (fun (t : Pt × Fin 255) => jointLadderBody tables rb sb t.1 t.2) where
  localLength := 12
  localLength_eq := by
    intro t n
    obtain ⟨acc, j⟩ := t
    simp only [jointLadderBody, bind_snd, pure_snd,
      mux4W_localLength, elm_localLength, Circuit.localLength,
      Operations.append_localLength, Operations.localLength]

/-- The final ladder step: select `T_255` and assert the result equals `target`
via `elmTo`. -/
def jointLadderFinal (tables : Tables) (rb sb : Vector E 256) (acc target : Pt) : C Unit := do
  let t ← mux4W (rb.get ⟨0, by omega⟩) (sb.get ⟨0, by omega⟩)
    (tables.x0 255) (tables.x1 255) (tables.x2 255) (tables.x3 255)
  elmTo acc t target

/-- The joint ladder.  `acc0` is the initial accumulator `-H`; `rb`/`sb` hold the
`r` and `t = n - s` bits least significant first; `target` is `-ep`. -/
def jointLadder (acc0 : Pt) (tables : Tables) (rb sb : Vector E 256) (target : Pt) :
    C Unit := do
  let acc ← Circuit.foldlRange 255 acc0 (jointLadderBody tables rb sb)
    (jointLadderBody_constantLength tables rb sb)
  jointLadderFinal tables rb sb acc target

end StandardECDSA.Phases
