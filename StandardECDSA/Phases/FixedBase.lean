/-
# Fixed-base phase: `ep = H + [E]G`

Ported from the pinned `circuit_baseline` revision
(`3a1bd20749ae0b6400a158651dba64a2c5fc58ff`), `Baseline/Projected/Offset.lean`.

The phase starts from `H - S` with `S = [4·(4^128 - 1)/3]G` and adds, for each of
the 128 windows, the constant point `[(4 + d_i)·4^i]G` where
`d_i = eBit[2i] + 2·eBit[2i+1]`.  The prefix invariant (plan §5) is

```text
ep_k = H - S + Σ_{i<k} [(4 + d_i)·4^i]G,      ep_128 = H + [E]G
```

Cost: 1 initial `affAdd` plus 128 × (`muxConst4` + `affAdd`) = 644 allocations
and 644 rows.

Task T12 (fixed-base half).
-/

import StandardECDSA.Gadgets.Select
import StandardECDSA.Gadgets.Affine
import StandardECDSA.Math.FixedTables
import StandardECDSA.Gadgets.LocalLength
import StandardECDSA.Gadgets.SelectW

namespace StandardECDSA.Phases

open StandardECDSA.Gadgets

/-- One window of the fixed-base phase: add `[(4 + d_i)·4^i]G` to `ep`. -/
def fixedBaseBody (eb : Vector E 256) (tables : Array (Array (Fp × Fp))) (ep : Pt)
    (i : Fin 128) : C Pt := do
  let t ← muxConst4W (eb.get ⟨2 * i.val, by omega⟩) (eb.get ⟨2 * i.val + 1, by omega⟩)
    (tables.getD i.val #[])
  affAdd ep t

/-- Every window of the fixed-base phase allocates exactly five wires. -/
def fixedBaseBody_constantLength (eb : Vector E 256) (tables : Array (Array (Fp × Fp))) :
    Circuit.ConstantLength (fun (t : Pt × Fin 128) => fixedBaseBody eb tables t.1 t.2) where
  localLength := 5
  localLength_eq := by
    intro t n
    obtain ⟨ep, j⟩ := t
    simp only [fixedBaseBody, bind_snd, pure_snd,
      muxConst4W_localLength, affAdd_localLength,
      Circuit.localLength, Operations.append_localLength, Operations.localLength]

/-- The fixed-base phase.  `eb` holds the 256 digest bits, least significant
first.  Returns `ep = H + [E]G` in affine coordinates. -/
def fixedBase (h : Pt) (eb : Vector E 256) : C Pt := do
  let shift := StandardECDSA.Math.FixedTables.fixedShift
  let tables := StandardECDSA.Math.FixedTables.fixedTables
  let ep0 ← affAdd h (cst shift.1, cst (-shift.2))
  Circuit.foldlRange 128 ep0 (fixedBaseBody eb tables)
    (fixedBaseBody_constantLength eb tables)

end StandardECDSA.Phases
