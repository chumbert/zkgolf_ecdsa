/-
# Fixed generator tables and the fixed-base shift

Ported from the pinned `circuit_baseline` revision
(`3a1bd20749ae0b6400a158651dba64a2c5fc58ff`), `Baseline/Projected/Offset.lean`
(`KP`, `affine`, `gPoint`, `mulG`, `fixedTables`, `fixedShift`).

The fixed-base phase consumes, for each window `i < 128` and digit `d ∈ {0,1,2,3}`,
the affine point `[(4 + d)·4^i]G`, and starts from the shift
`S = [4·(4^128 - 1)/3]G` so that the prefix invariant of plan §5 holds.

Task T11 certifies each of the `128·4` entries and the shift in the kernel; this
module only *defines* them, so that the circuit of task T05/T12 can run.
-/

import StandardECDSA.Gadgets.Field
import ECDSA.EC

namespace StandardECDSA.Math.FixedTables

open StandardECDSA.Gadgets

abbrev KP := ProjectivePoint Fp

/-- Affine coordinates of a finite projective point. -/
def affine (p : KP) : Fp × Fp := (p.X * p.Z⁻¹, p.Y * p.Z⁻¹)

/-- The P-256 generator in projective coordinates. -/
def gPoint : KP := { X := gx, Y := gy, Z := 1 }

/-- `[k]G` for a natural number `k`, reduced modulo the group order. -/
def mulG (k : Nat) : KP :=
  bsmul (padBits (natToBits (k % Challenge.Specs.ECDSAP256.n)) 256)
    gPoint Challenge.Specs.ECDSAP256.params

/-- Constants only: `[(4+d)·4^i]G` for `d = 0..3`; none is infinity. -/
def fixedTables : Array (Array (Fp × Fp)) :=
  (List.range 128).toArray.map fun i =>
    (List.range 4).toArray.map fun d => affine (mulG ((4 + d) * 4 ^ i))

/-- The fixed-base shift `S = [4·(4^128 - 1)/3]G`. -/
def fixedShift : Fp × Fp := affine (mulG (4 * ((4 ^ 128 - 1) / 3)))

end StandardECDSA.Math.FixedTables
