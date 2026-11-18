/-
# Standard P-256 ECDSA verification specification

This module defines the standard ECDSA verification predicate on P-256,
independent of any circuit internals.  It uses the vendored Longfellow
`AffinePoint`/`CurveParameters`/`ProjectivePoint` types for the group operations
but states the predicate purely in terms of group and scalar semantics.

Two predicates are provided:

* `standardVerify` — the textbook ECDSA verification equation
  `V = [u₁]G + [u₂]Q` with `u₁ = E·s⁻¹`, `u₂ = r·s⁻¹` mod `n`;
* `signaturePointVerify` — the equivalent "signature point" form
  `∃ R, [E]G + [r]Q + [t]R = O` with `t = n - s`, which is the shape the
  smaller circuit proves.

The equivalence of the two is task T03 (`Math/SignatureEquation.lean`); it is
*not* assumed here.

No circuit imports are used in this file.
-/

import ECDSA.EC
import ECDSA.Nat
import ECDSA.Pratt

namespace StandardECDSA

open ECDSA

/-! ## P-256 parameters -/

/-- The P-256 base field characteristic. -/
abbrev p : Nat := 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF

/-- The P-256 group order. -/
abbrev n : Nat := 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551

/-- The P-256 base field. -/
abbrev K := ZMod p

instance : Fact (Nat.Prime p) :=
  ⟨ECDSA.prime_115792089210356248762697446949407573530086143415290314195533631308867097853951⟩

/-- The P-256 curve parameters. -/
def params : CurveParameters K := {
  a := -3
  b := 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
  gx := 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
  gy := 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
  kBits := 256 }

/-- The P-256 generator, in projective coordinates. -/
def gPoint : ProjectivePoint K := { X := params.gx, Y := params.gy, Z := 1 }

/-! ## Digest encoding -/

/-- A 256-bit digest split into two 128-bit limbs.
`E = val(digestLo) + 2^128 * val(digestHi)` is the big-endian integer
represented by the 32-byte digest.  Each limb is below `2^128`. -/
structure Digest where
  lo : K
  hi : K

/-- The natural number represented by a digest pair. -/
def Digest.toNat (d : Digest) : Nat := d.lo.val + 2 ^ 128 * d.hi.val

/-! ## Scalar helpers -/

/-- The inverse of `a` modulo `n`, as a natural number in `[0, n)`. -/
def invModN (a : Nat) : Nat := ((a : ZMod n)⁻¹).val

/-- Scalar multiplication of the generator by a natural number. -/
def mulG (k : Nat) : ProjectivePoint K :=
  bsmul (padBits (natToBits (k % n)) 256) gPoint params

/-- Scalar multiplication of an arbitrary projective point. -/
def mulP (k : Nat) (P : ProjectivePoint K) : ProjectivePoint K :=
  bsmul (padBits (natToBits (k % n)) 256) P params

/-- The affine `x`-coordinate of a finite projective point. -/
def affineX (P : ProjectivePoint K) : K := P.X * P.Z⁻¹

/-! ## The standard verification predicate -/

/-- The standard P-256 ECDSA verification predicate.

Given public key `Q = (pkX, pkY)`, a 256-bit digest `E` (as two limbs), and a
signature `(r, s)` whose canonical representatives are the scalar values:

1. `Q` is an affine on-curve point (hence not `O`);
2. `0 < r < n` and `0 < s < n`;
3. `w = s⁻¹ mod n`, `u₁ = E·w mod n`, `u₂ = r·w mod n`;
4. `V = [u₁]G + [u₂]Q`;
5. `V ≠ O` and `val(x(V)) mod n = r`.

Both high-`s` and low-`s` signatures are accepted.  There is no
original-table finiteness restriction and no requirement `pkX ≠ 0`.
-/
def standardVerify (pkX pkY digestLo digestHi r s : K) : Prop :=
  let Q : AffinePoint K := { X := pkX, Y := pkY }
  Q.IsOnCurve params ∧
  0 < r.val ∧ r.val < n ∧ 0 < s.val ∧ s.val < n ∧
  let E := (Digest.mk digestLo digestHi).toNat
  let w := invModN s.val
  let u1 := (E * w) % n
  let u2 := (r.val * w) % n
  let V := addE (mulG u1) (mulP u2 Q.toProjective) params
  ¬ ProjectiveEquiv V infinityPoint ∧ (affineX V).val % n = r.val

/-! ## The signature-point form used by the circuit -/

/-- The "signature point" form of verification: there is a finite on-curve point
`R` with `[E]G + [r]Q + [t]R = O` and `val(R.x) mod n = r`, where `t = n - s`.

This is the shape the smaller circuit proves.  `Math/SignatureEquation.lean`
(T03) proves it equivalent to `standardVerify`. -/
def signaturePointVerify (pkX pkY digestLo digestHi r s : K) : Prop :=
  let Q : AffinePoint K := { X := pkX, Y := pkY }
  Q.IsOnCurve params ∧
  0 < r.val ∧ r.val < n ∧ 0 < s.val ∧ s.val < n ∧
  let E := (Digest.mk digestLo digestHi).toNat
  let t := n - s.val
  ∃ R : AffinePoint K,
    R.IsOnCurve params ∧
    ProjectiveEquiv
      (addE (addE (mulG E) (mulP r.val Q.toProjective) params)
        (mulP t R.toProjective) params)
      infinityPoint ∧
    R.X.val % n = r.val

end StandardECDSA
