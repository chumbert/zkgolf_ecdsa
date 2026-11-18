/-
# Field-level lowering helpers for the standard P-256 ECDSA circuit

Ported from the pinned `circuit_baseline` revision
(`3a1bd20749ae0b6400a158651dba64a2c5fc58ff`), `Baseline/Circuit.lean`, with the
namespace renamed to `StandardECDSA.Gadgets` so that it does not collide with
this branch's own `Baseline` library (which is the 18,612-cost pointwise
challenge submission, a different circuit).

Lowering conventions (all mechanical, none of them an optimisation of the
*algorithm*):

* addition, subtraction and multiplication by a constant are free (linear);
* a product of two non-constant affine forms is one R1CS row; its result costs
  one witness allocation if it is later used as a multiplication operand
  (`mat`);
* an assertion `Σ products + affine = 0` keeps exactly one product inside its
  own row and allocates the others (`assertZeroLazy`);
* products with a constant operand fold away.

This file owns the *shared* lowering vocabulary (`E`, `C`, `cst`, `sc`, `mat`,
`mm`, `pm`, `assertZeroLazy`) plus the curve constants and the two field-level
assertions (`isOnCurve`, `pointEquality`) and the nonzero gadget.  Task T05.
-/

import Challenge.Instances.ECDSA_P256_Digest.Interface
import Challenge.Utils.CostR1CS

namespace StandardECDSA.Gadgets

open Challenge.Instances.ECDSA_P256_Digest.Interface

abbrev Fp := F circuitPrime
abbrev E := Expression Fp
abbrev C := Circuit Fp

/-- An affine point represented by two expressions. -/
abbrev Pt := E × E

def deg : E → ℕ := Challenge.CostR1CS.degree

/-- A constant expression. -/
def cst (c : Fp) : E := .const c

/-- Multiplication by a constant: linear, hence free. -/
def sc (c : Fp) (e : E) : E := .mul (.const c) e

/-- Evaluate an expression in the all-zero environment; only meaningful for
constant expressions. -/
def constVal (e : E) : Fp := e.eval ⟨fun _ => 0, fun _ _ => #[]⟩

/-- Make `e` affine by giving every product term its own wire
(1 allocation + 1 row each). -/
def mat : E → C E
  | .var v => pure (.var v)
  | .const c => pure (.const c)
  | .add a b => do
      let a' ← mat a
      let b' ← mat b
      pure (a' + b')
  | .mul a b => do
      let a' ← mat a
      let b' ← mat b
      if deg a' = 0 ∨ deg b' = 0 then pure (.mul a' b')
      else do
        let w ← Circuit.witnessField (.mul (.expr a') (.expr b'))
        Circuit.assertZero (.mul a' b' - w)
        pure w

/-- Product that is allocated immediately. -/
def mm (a b : E) : C E := mat (.mul a b)

/-- Product left pending (free until it is consumed by `mat` or an assertion). -/
def pm (a b : E) : E := .mul a b

/-- Flatten an expression into (coefficient, term) items; a term is a leaf or a
product of two non-constant factors. -/
def flat (c : Fp) : E → List (Fp × E)
  | .add a b => flat c a ++ flat c b
  | .mul a b =>
      if deg a = 0 then flat (c * constVal a) b
      else if deg b = 0 then flat (c * constVal b) a
      else [(c, .mul a b)]
  | e => [(c, e)]

def isProd : E → Bool
  | .mul _ _ => true
  | _ => false

/-- Assert `e = 0`: one product stays in the assertion's own row, the rest get
wires. -/
def assertZeroLazy (e : E) : C Unit := do
  let items := flat 1 e
  let prods := items.filter (fun it => isProd it.2)
  let lins := items.filter (fun it => !isProd it.2)
  match prods with
  | [] => Circuit.assertZero e
  | (c, .mul a b) :: rest => do
      let a' ← mat a
      let b' ← mat b
      let mut acc : E := sc c (.mul a' b')
      for (c', t) in rest do
        let w ← mat t
        acc := acc + sc c' w
      for (c', t) in lins do
        acc := acc + sc c' t
      Circuit.assertZero acc
  | _ => pure ()

/-! ## Curve constants -/

def pa : Fp := Challenge.Specs.ECDSAP256.params.a
def pb : Fp := Challenge.Specs.ECDSAP256.params.b
def k3b : Fp := pb + pb + pb
def gx : Fp := Challenge.Specs.ECDSAP256.params.gx
def gy : Fp := Challenge.Specs.ECDSAP256.params.gy

/-! ## Field-level assertions -/

/-- `y² = x³ + a·x + b`, i.e. the affine point `(x, y)` is on the curve. -/
def isOnCurve (x y : E) : C Unit := do
  let xx ← mm x x
  assertZeroLazy (.mul y y - (.mul x xx + sc pa x + cst pb))

/-- Projective point equality against an affine point: `(x, y, z) = (px, py)`. -/
def pointEquality (x y z px py : E) : C Unit := do
  let z' ← mat z
  assertZeroLazy (x - .mul z' px)
  assertZeroLazy (y - .mul z' py)

/-- Nonzero assertion: allocate an inverse witness and constrain `x · x⁻¹ = 1`.
Witness computation alone is *not* a nonzero assertion; the row is. -/
def nonzero (x : E) : C E := do
  let inv ← Circuit.witnessField (.inv (.expr x))
  Circuit.assertZero (pm x inv - cst 1)
  pure inv

end StandardECDSA.Gadgets
