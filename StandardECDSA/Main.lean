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
import StandardECDSA.Phases.Cost
import StandardECDSA.Phases.Semantics
import StandardECDSA.Phases.TableSemantics

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

/-- The per-bit body of a 256-bit hint vector: allocate the hint cell and assert
that it is Boolean. -/
def bitBody (base stride : Nat) (i : Fin 256) : C E := do
  let b ← hint (base + stride * i.val)
  Gadgets.assertBool b
  pure b

/-- Every bit body allocates exactly one wire and one row. -/
def bitBody_constantLength (base stride : Nat) : Circuit.ConstantLength (bitBody base stride) where
  localLength := 1
  localLength_eq := by
    intro i n
    simp only [bitBody, hint, Gadgets.assertBool, Circuit.localLength, bind_snd, pure_snd,
      witnessField_snd, assertZero_snd, localLength_witness, localLength_assert,
      Operations.append_localLength, Operations.localLength, Nat.add_zero, Nat.zero_add]

/-- A 256-bit hint vector. -/
def bitVec (base stride : Nat) : C (Vector E 256) :=
  Circuit.mapFinRange 256 (bitBody base stride) (bitBody_constantLength base stride)

/-- Every entry of a `bitVec` is a wire. -/
theorem bitVec_deg (base stride n : Nat) (k : Fin 256) :
    deg ((Circuit.output (bitVec base stride) n).get k) = 1 := by
  rw [bitVec, Circuit.mapFinRange.output_eq]
  simp only [Vector.getElem_mapFinRange, Vector.get_eq_getElem]
  simp only [bitBody, hint, output_bind, output_pure, output_witnessField, deg,
    Challenge.CostR1CS.degree]

/-- Little-endian linear combination `sum_{j < len} 2^j * v[lo + j]`. -/
def linComb (v : Vector E 256) (lo len : Nat) : E :=
  (List.range len).foldl
    (fun acc j => acc + sc ((2 : Fp) ^ j) (v.getD (lo + j) (cst 0))) (cst 0)

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
  let eb ← bitVec 4 3
  let rb ← bitVec 5 3
  let sb ← bitVec 6 3
  -- digest binding, split into two 128-bit limbs
  Circuit.assertZero (linComb eb 0 128 - inp.digestLo)
  Circuit.assertZero (linComb eb 128 128 - inp.digestHi)
  -- scalar bindings
  Circuit.assertZero (linComb rb 0 256 - inp.r)
  Circuit.assertZero (linComb sb 0 256 - negS)
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
