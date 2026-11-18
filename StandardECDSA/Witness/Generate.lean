/-
# Honest seed generation (task T16)

The executable witness generator.  Given the six external inputs
`(pkX, pkY, digestLo, digestHi, r, s)` and a bad-equation family, it

1. computes the standard verification point `V = [u₁]G + [u₂]Q`
   (`Math/SignatureEquation.lean`, `stdV`);
2. takes the signature point `R = V` and extracts its `y`-coordinate;
3. extracts the canonical overflow bit `overflow` with `rx = r + n·overflow`;
4. extracts the 256 little-endian bits of `r`, of `t = n - s` and of the digest
   `E = val(digestLo) + 2^128·val(digestHi)`;
5. selects the first good offset `H = [k+1]G` by the bounded search
   `findGoodOffset` of `Math/OffsetCandidates.lean`.

The result is the typed 772-field `Seed` of `Witness/Seed.lean`.  Nothing here
mentions constraint satisfaction: the seed is a mathematical object, and
`Witness/Correctness.lean` proves it admissible whenever the input is
standard-valid.
-/

import StandardECDSA.Math.OffsetCandidates
import StandardECDSA.Math.SignatureEquation
import StandardECDSA.Witness.Seed

namespace StandardECDSA.Witness

open StandardECDSA
open StandardECDSA.Math

set_option maxRecDepth 100000

/-! ## Bit and digest extraction -/

/-- The digest integer `E = val(lo) + 2^128 · val(hi)`. -/
def digestOf (lo hi : K) : Nat := lo.val + 2 ^ 128 * hi.val

/-- The `i`-th little-endian bit of `m`. -/
def bitOf (m i : Nat) : Nat := (m / 2 ^ i) % 2

/-- The 256 little-endian bits of `m`, as field elements. -/
def bitsOf (m : Nat) : Fin 256 → K := fun i => ((bitOf m (i : Nat) : Nat) : K)

/-- The canonical overflow bit for `rx = r + n·overflow`. -/
def overflowOf (rx r : Nat) : Nat := if rx < n then 0 else 1

/-- The offset point `[k+1]G` in the vendored projective representation. -/
def offsetPt (k : Nat) : ProjectivePoint K := FixedTables.mulG (k + 1)

/-! ## The generator -/

/-- **The honest seed generator.**  All 772 hint cells are computed from the six
external inputs and the selected offset. -/
noncomputable def generateSeed (pkX pkY digestLo digestHi r s : K)
    (fam : BadFamily Grp) (hm : fam.m < 1040) : Seed :=
  let Q : AffinePoint K := { X := pkX, Y := pkY }
  let E := digestOf digestLo digestHi
  let V := stdV Q r s E
  let Hp := offsetPt (findGoodOffset fam hm).val
  { ry := V.Y * V.Z⁻¹
    hx := Hp.X * Hp.Z⁻¹
    hy := Hp.Y * Hp.Z⁻¹
    overflow := ((overflowOf (affineX V).val r.val : Nat) : K)
    rBits := bitsOf r.val
    tBits := bitsOf (n - s.val)
    digestBits := bitsOf E }

/-- The offset index chosen by the generator. -/
theorem generateSeed_index_lt (pkX pkY digestLo digestHi r s : K)
    (fam : BadFamily Grp) (hm : fam.m < 1040) :
    (findGoodOffset fam hm).val < 1040 :=
  (findGoodOffset fam hm).isLt

/-- The offset point chosen by the generator is finite. -/
theorem generateSeed_offsetPt_Z_ne_zero (pkX pkY digestLo digestHi r s : K)
    (fam : BadFamily Grp) (hm : fam.m < 1040) :
    (offsetPt (findGoodOffset fam hm).val).Z ≠ 0 := by
  have hk := generateSeed_index_lt pkX pkY digestLo digestHi r s fam hm
  have hn := thousand_forty_lt_n
  exact FixedTables.mulG_Z_ne_zero (by omega) (by omega)

/-- The offset point chosen by the generator is on the curve. -/
theorem generateSeed_offsetPt_on_curve (pkX pkY digestLo digestHi r s : K)
    (fam : BadFamily Grp) (hm : fam.m < 1040) :
    (offsetPt (findGoodOffset fam hm).val).IsOnCurve params :=
  FixedTables.mulG_on_curve _

/-- The offset point chosen by the generator is the candidate `[k+1]G`. -/
theorem generateSeed_offsetPt_toMathlib (pkX pkY digestLo digestHi r s : K)
    (fam : BadFamily Grp) (hm : fam.m < 1040) :
    (offsetPt (findGoodOffset fam hm).val).toMathlibPoint params
        (generateSeed_offsetPt_on_curve pkX pkY digestLo digestHi r s fam hm)
      = offsetCandidate (findGoodOffset fam hm) := by
  rw [toMathlibPoint_proof_irrel (offsetPt (findGoodOffset fam hm).val)
    (generateSeed_offsetPt_on_curve pkX pkY digestLo digestHi r s fam hm)
    (FixedTables.mulG_on_curve _)]
  exact FixedTables.mulG_toMathlib _

end StandardECDSA.Witness
