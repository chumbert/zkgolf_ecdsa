/-
# Independent standard P-256 ECDSA verifier (test oracle)

A *deliberately independent* implementation of standard P-256 ECDSA
verification, written from the textbook affine group law with `ZMod p` field
arithmetic.  It shares no code with the circuit under test (which uses the
vendored Longfellow projective RCB formulas) and no code with the vendored
`ECDSA` library, so agreement between the two is evidence about the circuit
rather than a tautology.

This is a test oracle only.  The trusted statement is the proved theorem
`StandardECDSA.main_accepts_iff_standard`; this file exists so that the
executable regression suite (T19) can compare the circuit against an
implementation that was not derived from it.

Task T19.
-/
import StandardECDSA.Math.GroupOrder
import Challenge.Specs.ECDSAP256

namespace Tests.StandardECDSA.Oracle

open Challenge.Specs.ECDSAP256

/-- An affine point over `F_p`; `none` is the point at infinity. -/
abbrev APt := Option (ZMod p × ZMod p)

/-- The curve equation `y² = x³ - 3x + b`. -/
def onCurve (x y : ZMod p) : Bool := y * y == x * x * x + params.a * x + params.b

/-- The affine group law, with the standard exceptional cases. -/
def addA : APt → APt → APt
  | none, q => q
  | q, none => q
  | some (x1, y1), some (x2, y2) =>
      if x1 == x2 then
        if y1 + y2 == 0 then none
        else
          let l := (3 * x1 * x1 + params.a) / (2 * y1)
          let x3 := l * l - 2 * x1
          some (x3, l * (x1 - x3) - y1)
      else
        let l := (y2 - y1) / (x2 - x1)
        let x3 := l * l - x1 - x2
        some (x3, l * (x1 - x3) - y1)

/-- Negation. -/
def negA : APt → APt
  | none => none
  | some (x, y) => some (x, -y)

/-- Subtraction. -/
def subA (P Q : APt) : APt := addA P (negA Q)

/-- Scalar multiplication by double-and-add, most significant bit first. -/
def mulA (k : Nat) (P : APt) : APt :=
  (List.range 256).foldl
    (fun acc i =>
      let acc := addA acc acc
      if (k / 2 ^ (255 - i)) % 2 == 1 then addA acc P else acc) none

/-- The standard base point. -/
def gA : APt := some (params.gx, params.gy)

/-- `a⁻¹ mod n`, as a natural number. -/
def invN (a : Nat) : Nat := ((a : ZMod n))⁻¹.val

/-- The standard verification point `V = [u₁]G + [u₂]Q` with
`u₁ = e·s⁻¹`, `u₂ = r·s⁻¹` (mod `n`). -/
def verifyPoint (pkx pky E r s : Nat) : APt :=
  let w := invN s
  let u1 := (E % n) * w % n
  let u2 := r * w % n
  addA (mulA u1 gA) (mulA u2 (some ((pkx : ZMod p), (pky : ZMod p))))

/-- Standard P-256 ECDSA verification: `r, s ∈ [1, n-1]`, `Q` on the curve,
`V ≠ O` and `x(V) mod n = r`. -/
def verify (pkx pky E r s : Nat) : Bool :=
  if !(pkx < p && pky < p) then false
  else if !(0 < r && r < n && 0 < s && s < n) then false
  else if !onCurve (pkx : ZMod p) (pky : ZMod p) then false
  else
    match verifyPoint pkx pky E r s with
    | none => false
    | some (vx, _) => vx.val % n == r

/-- A square root in `F_p`, using `p ≡ 3 (mod 4)`. -/
def sqrtModP (a : ZMod p) : Option (ZMod p) :=
  let y := a ^ ((p + 1) / 4)
  if y * y == a then some y else none

/-- The affine curve point with the given `x`-coordinate, if one exists. -/
def pointOfX (x : Nat) : Option (ZMod p × ZMod p) :=
  let xf : ZMod p := x
  (sqrtModP (xf * xf * xf + params.a * xf + params.b)).map fun y => (xf, y)

/-- The smallest `x ≥ n` that is the `x`-coordinate of a curve point, searched
over `[n, n + fuel)`.  Such an `x` exists: the interval `[n, p)` has about
`2^130` elements and half of them are `x`-coordinates. -/
def findOverflowX (fuel : Nat) : Option (Nat × ZMod p) :=
  let rec go : Nat → Option (Nat × ZMod p)
    | 0 => none
    | k + 1 =>
        let x := n + (fuel - k)
        match pointOfX x with
        | some (_, y) => some (x, y)
        | none => go k
  go fuel

/-- Sign with private key `d` and nonce `k` on digest `E`: returns
`(Q.x, Q.y, r, s)`. -/
def signWith (d k E : Nat) : Option (Nat × Nat × Nat × Nat) := do
  let Q ← mulA d gA
  let R ← mulA k gA
  let r := R.1.val % n
  if r == 0 then none else
  let s := invN k * ((E + r * d) % n) % n
  if s == 0 then none else
  some (Q.1.val, Q.2.val, r, s)

end Tests.StandardECDSA.Oracle
