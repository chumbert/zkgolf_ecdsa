/-
# Standard P-256 ECDSA circuit: assembly

This module assembles the standard P-256 ECDSA circuit from the bundled
gadgets and phases, and (from milestone M5 on) exports its correctness
theorems.

## The circuit

Six base-field inputs `(pkX, pkY, digestLo, digestHi, r, s)`, unit output.
The auxiliary data is supplied through the 772-cell hint seed of
`Witness/Seed.lean`:

| index | component |
|---|---|
| 0 | `ry`, the `y`-coordinate of the signature point `R` |
| 1, 2 | `Hx, Hy`, the offset point `H` |
| 3 | `overflow`, the Boolean selecting `R.x = r + n·overflow` |
| `4 + 3i`, `5 + 3i`, `6 + 3i` | `eBit[i]`, `rBit[i]`, `tBit[i]` for `i < 256` |

## Phases

1. **Scalar phase** (`Gadgets/Scalar.lean`): Boolean constraints on the 769
   scalar bits, the two digest-limb bindings, the `r` and `t = n - s`
   bindings, two ordinary order comparisons `r, t < n`, and the guarded
   comparison `overflow = 1 → r < p - n`.
2. **Fixed-base phase** (`Phases/FixedBase.lean`): `ep = H + [E]G`.
3. **Shifted-table phase** (`Phases/ShiftedTables.lean`): `±3H` plus `Q`, `R`.
4. **Joint ladder** (`Phases/JointLadder.lean`): `[r]Q + [t]R - H`, asserted
   against `-ep`.

## Cost

The measured cost is reported by `lake exe standardEcdsaCheck --count-only`.
The plan's proposed budget is 4,628 allocations + 4,634 rows = 9,262.
-/

import StandardECDSA.Interface
import StandardECDSA.Spec
import StandardECDSA.HintCausality
import StandardECDSA.Math.P256
import StandardECDSA.Math.GroupOrder
import StandardECDSA.Math.ScalarEncoding
import StandardECDSA.Math.ConstantBounds
import StandardECDSA.Math.OffsetConditions
import StandardECDSA.Math.FixedTables
import StandardECDSA.Witness.Seed
import StandardECDSA.Gadgets.Field
import StandardECDSA.Gadgets.Select
import StandardECDSA.Gadgets.Scalar
import StandardECDSA.Gadgets.Affine
import StandardECDSA.Gadgets.ELM
import StandardECDSA.Gadgets.Lemmas
import StandardECDSA.Gadgets.Cost
import StandardECDSA.Gadgets.R1CS
import StandardECDSA.Gadgets.LtExplicit
import StandardECDSA.Math.ElmAlgebra
import StandardECDSA.Math.AffineBridge
import StandardECDSA.Phases.FixedBase
import StandardECDSA.Phases.ShiftedTables
import StandardECDSA.Phases.JointLadder

namespace StandardECDSA

open StandardECDSA.Gadgets
open StandardECDSA.Phases

/-- The hint provider key for the standard circuit's seed. -/
def hintKey : String := "standard"

/-- Read seed cell `i`. -/
def hint (i : Nat) : C E :=
  Circuit.witnessField (.hintGet hintKey 1 (.const i.toUInt64) ⟨0, by decide⟩)

/-- The P-256 group order as a field element. -/
def nFp : Fp := (Challenge.Specs.ECDSAP256.n : Fp)

/-- The standard P-256 ECDSA circuit. -/
def main (inp : Var Input Fp) : C Unit := do
  -- seed: R.y, H, overflow
  let ry ← hint 0
  let hx ← hint 1
  let hy ← hint 2
  let overflow ← hint 3
  Gadgets.assertBool overflow
  -- the signature point R has x-coordinate r + n·overflow
  let rx := inp.r + sc nFp overflow
  let q : Pt := (inp.pkX, inp.pkY)
  let r : Pt := (rx, ry)
  let h : Pt := (hx, hy)
  isOnCurve q.1 q.2
  isOnCurve r.1 r.2
  isOnCurve h.1 h.2
  -- nonzero r and t = n - s
  let _ ← nonzero inp.r
  let negS := cst (Challenge.Specs.ECDSAP256.n : Fp) - inp.s
  let _ ← nonzero negS
  -- scalar bits
  let mut eb : Array E := #[]
  let mut rb : Array E := #[]
  let mut sb : Array E := #[]
  let mut eeLo := cst 0
  let mut eeHi := cst 0
  let mut rr := cst 0
  let mut ss := cst 0
  for i in [0:256] do
    let be ← hint (4 + 3 * i)
    let br ← hint (5 + 3 * i)
    let bs ← hint (6 + 3 * i)
    Gadgets.assertBool be
    Gadgets.assertBool br
    Gadgets.assertBool bs
    eb := eb.push be
    rb := rb.push br
    sb := sb.push bs
    if i < 128 then
      eeLo := eeLo + sc ((2 : Fp) ^ i) be
    else
      eeHi := eeHi + sc ((2 : Fp) ^ (i - 128)) be
    rr := rr + sc ((2 : Fp) ^ i) br
    ss := ss + sc ((2 : Fp) ^ i) bs
  -- digest binding, split into two 128-bit limbs
  Circuit.assertZero (eeLo - inp.digestLo)
  Circuit.assertZero (eeHi - inp.digestHi)
  -- scalar bindings
  Circuit.assertZero (rr - inp.r)
  Circuit.assertZero (ss - negS)
  -- order comparisons
  assertLtOrderOf nSubOne (fun i => rb.getD i (cst 0))
  assertLtOrderOf nSubOne (fun i => sb.getD i (cst 0))
  -- guarded lift comparison: overflow = 1 → r < p - n
  assertLtOrderGuardedOf pSubNSubOne overflow (fun i => rb.getD i (cst 0))
  -- phases
  let ep ← fixedBase h eb
  let tables ← shiftedTables h q r
  jointLadder (hx, -hy) tables rb sb (ep.1, -ep.2)

end StandardECDSA
