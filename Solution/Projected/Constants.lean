import Solution.Projected.Types
import ECDSA.Ecdsa

/-! Fixed-base constant tables, computed exactly as in the experimental circuit.
(T0.3 replaces these with literal tables; the values are identical.) -/
namespace Solution.Projected

open Challenge.Specs.ECDSAP256

abbrev KP := ProjectivePoint Fp

def affine (p : KP) : Fp × Fp := (p.X * p.Z⁻¹, p.Y * p.Z⁻¹)
def gPoint : KP := { X := gx, Y := gy, Z := 1 }
def mulG (k : Nat) : KP :=
  bsmul (padBits (natToBits (k % n)) 256) gPoint params

/-- Constants only: [(4+d)4^i G] for d=0..3; none is infinity. -/
def fixedTables : Array (Array (Fp × Fp)) :=
  (List.range 128).toArray.map fun i =>
    (List.range 4).toArray.map fun d => affine (mulG ((4+d)*4^i))

def fixedShift : Fp × Fp := affine (mulG (4 * ((4^128 - 1)/3)))

end Solution.Projected
