/-
# Witness seed: the typed 772-field hint layout

The standard circuit's prover hints are laid out as a fixed, versioned record of
772 field elements:

| component | count |
|---|---|
| `ry` (the `y`-coordinate of the signature point `R`) | 1 |
| `hx`, `hy` (the offset `H`) | 2 |
| `overflow` (the `r + n·overflow` branch bit) | 1 |
| `rBits` (256 bits of `r`) | 256 |
| `tBits` (256 bits of `t = n - s`) | 256 |
| `digestBits` (256 bits of the digest `E`) | 256 |
| **total** | **772** |

All hint cells are counted as allocations; only the six external inputs are
excluded from the cost.
-/

import StandardECDSA.Math.OffsetConditions
import StandardECDSA.Math.ScalarEncoding

namespace StandardECDSA.Witness

open StandardECDSA

set_option maxRecDepth 100000

/-- The typed 772-field seed layout. -/
structure Seed where
  /-- The `y`-coordinate of the signature point `R`. -/
  ry : K
  /-- The `x`-coordinate of the offset `H`. -/
  hx : K
  /-- The `y`-coordinate of the offset `H`. -/
  hy : K
  /-- The `r + n·overflow` branch bit. -/
  overflow : K
  /-- The 256 bits of `r`, little-endian. -/
  rBits : Fin 256 → K
  /-- The 256 bits of `t = n - s`, little-endian. -/
  tBits : Fin 256 → K
  /-- The 256 bits of the digest `E`, little-endian. -/
  digestBits : Fin 256 → K

/-- The seed has exactly 772 field elements. -/
theorem seed_field_count : 4 + 256 + 256 + 256 = 772 := by norm_num

/-- The offset carried by a seed. -/
def Seed.H (s : Seed) : AffinePoint K := { X := s.hx, Y := s.hy }

/-- The signature point carried by a seed. -/
def Seed.R (s : Seed) (rx : K) : AffinePoint K := { X := rx, Y := s.ry }

/-- The scalar facts a seed must witness: the bits are Boolean, they recompose to
`r`, `t` and the digest limbs, and the overflow bit is Boolean. -/
structure ScalarFacts (s : Seed) (E r t : Nat) : Prop where
  /-- The overflow bit is Boolean. -/
  overflow_bool : s.overflow = 0 ∨ s.overflow = 1
  /-- The `r` bits are Boolean. -/
  rBits_bool : ∀ i, s.rBits i = 0 ∨ s.rBits i = 1
  /-- The `t` bits are Boolean. -/
  tBits_bool : ∀ i, s.tBits i = 0 ∨ s.tBits i = 1
  /-- The digest bits are Boolean. -/
  digestBits_bool : ∀ i, s.digestBits i = 0 ∨ s.digestBits i = 1
  /-- The `r` bits recompose to `r`. -/
  rBits_val : StandardECDSA.Math.leNat (fun i => (s.rBits i).val) = r
  /-- The `t` bits recompose to `t`. -/
  tBits_val : StandardECDSA.Math.leNat (fun i => (s.tBits i).val) = t
  /-- The low digest limb is the low half of the digest bits. -/
  digestLo_val : StandardECDSA.Math.leNat (fun i : Fin 128 => (s.digestBits (Fin.castLE (by norm_num) i)).val) = E % 2 ^ 128
  /-- The high digest limb is the high half of the digest bits. -/
  digestHi_val : StandardECDSA.Math.leNat (fun i : Fin 128 => (s.digestBits (Fin.natAdd 128 i)).val)
    = E / 2 ^ 128

/-- A seed is *admissible* for the given signature data when its scalar facts
hold and its offset is geometrically good.  This is a mathematical predicate on
group points and naturals; it never mentions constraint satisfaction. -/
def Admissible (s : Seed) (_rx : K) (E r t : Nat)
    (hH : (s.H).IsOnCurve params)
    (fam : StandardECDSA.Math.BadFamily (params.toMathlib).toProjective.Point) : Prop :=
  ScalarFacts s E r t ∧
  StandardECDSA.Math.GoodOffset s.H hH fam

end StandardECDSA.Witness
