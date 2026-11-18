/-
# Standard P-256 ECDSA circuit interface

This module fixes the six-input external interface of the standard P-256 ECDSA
circuit and the prover/verifier contracts.

The six base-field inputs, in fixed documented order:

```text
(pkX, pkY, digestLo, digestHi, r, s) : F_p^6
```

The circuit proves that each digest limb is below `2^128` by binding it to 128
Boolean digest bits.  Define `E = val(digestLo) + 2^128 * val(digestHi)`.  The
scalar inputs denote their canonical field representatives.  The circuit
enforces `1 ≤ r < n` and `1 ≤ s < n`.  The output is unit: satisfying the
constraints means verification succeeds.

Whether these six values are public or private in an enclosing ZK application
does not change the arithmetic relation or the allocation accounting.
-/

import StandardECDSA.Spec
import StandardECDSA.HintCausality
import Clean.Circuit

namespace StandardECDSA

open Circuit

/-! ## Six-input circuit interface -/

/-- The six external inputs to the standard ECDSA circuit.  All are base-field
elements. -/
structure Input (F : Type) where
  /-- The public key `x`-coordinate. -/
  pkX : F
  /-- The public key `y`-coordinate. -/
  pkY : F
  /-- The low 128 bits of the digest. -/
  digestLo : F
  /-- The high 128 bits of the digest. -/
  digestHi : F
  /-- The signature scalar `r`. -/
  r : F
  /-- The signature scalar `s`. -/
  s : F
  deriving ProvableStruct

/-- The output is unit: satisfying the constraints means verification succeeds. -/
abbrev Output : TypeMap := unit

/-- The circuit prime is the P-256 base field order. -/
abbrev circuitPrime : Nat := p

/-! ## Semantic contracts -/

/-- The specification: given the six inputs, the circuit's constraints hold iff
the standard ECDSA verification predicate holds. -/
def Spec (input : Input (F circuitPrime)) (_output : Output (F circuitPrime))
    (_data : ProverData (F circuitPrime)) : Prop :=
  standardVerify input.pkX input.pkY input.digestLo input.digestHi input.r input.s

/-- The signature-point form of the specification, which is the shape the
circuit's phases prove.  `Math/SignatureEquation.lean` (T03) proves it equivalent
to `Spec`. -/
def SpecSignaturePoint (input : Input (F circuitPrime)) (_output : Output (F circuitPrime))
    (_data : ProverData (F circuitPrime)) : Prop :=
  signaturePointVerify input.pkX input.pkY input.digestLo input.digestHi input.r input.s

/-- No caller assumptions beyond the six inputs being field elements. -/
def Assumptions (_input : Input (F circuitPrime)) (_data : ProverData (F circuitPrime)) : Prop :=
  True

/-- Prover assumptions: the standard verification predicate must hold.  This is
the *only* assumption made of the prover, and it is discharged by the caller of
the completeness theorem, never by the soundness theorem. -/
def ProverAssumptions (input : Input (F circuitPrime)) (data : ProverData (F circuitPrime))
    (_hint : ProverHint (F circuitPrime)) : Prop :=
  Spec input () data

/-- Prover spec: always true.  The circuit is deterministic given its hints, so
there is no additional prover-side obligation. -/
def ProverSpec (_input : Input (F circuitPrime)) (_output : Output (F circuitPrime))
    (_hint : ProverHint (F circuitPrime)) : Prop :=
  True

/-! ## The hint contract

The honest witness generator reads its hints through the 772-cell seed layout of
`Witness/Seed.lean`.  `HintCausality.lean` states the fixed-hint causality
contract for it.  We deliberately do **not** claim the old
`Circuit.ComputableWitnesses` obligation for a `hintGet` leaf: under the pinned
Clean definitions `ProverEnvironment.AgreesBelow` compares wires only, so that
obligation is not satisfiable for hint-backed leaves.
-/

/-- The number of hint cells the standard circuit allocates. -/
def hintCellCount : Nat := 772

/-- The hint cell count matches the seed layout. -/
theorem hintCellCount_eq : hintCellCount = 4 + 256 + 256 + 256 := rfl

end StandardECDSA
