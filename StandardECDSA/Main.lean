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
import StandardECDSA.Math.Compare
import StandardECDSA.Math.OffsetConditions
import StandardECDSA.Math.OffsetCandidates
import StandardECDSA.Math.SignatureEquation
import StandardECDSA.Math.FixedTables
import StandardECDSA.Witness.Seed
import StandardECDSA.Witness.Generate
import StandardECDSA.Witness.Correctness
import StandardECDSA.Gadgets.Field
import StandardECDSA.Gadgets.Select
import StandardECDSA.Gadgets.Scalar
import StandardECDSA.Gadgets.Affine
import StandardECDSA.Gadgets.ELM
import StandardECDSA.Gadgets.Lemmas
import StandardECDSA.Gadgets.Cost
import StandardECDSA.Gadgets.R1CS
import StandardECDSA.Gadgets.LtExplicit
import StandardECDSA.Gadgets.Semantics
import StandardECDSA.Gadgets.Semantics2
import StandardECDSA.Gadgets.Semantics3
import StandardECDSA.Gadgets.Semantics4
import StandardECDSA.Gadgets.Semantics6
import StandardECDSA.Gadgets.CurveExplicit
import StandardECDSA.Math.ElmAlgebra
import StandardECDSA.Math.AffineBridge
import StandardECDSA.Phases.FixedBase
import StandardECDSA.Phases.ShiftedTables
import StandardECDSA.Phases.JointLadder
import StandardECDSA.Phases.LadderSemantics
import StandardECDSA.Phases.Cost
import StandardECDSA.Phases.Semantics
import StandardECDSA.Phases.TableSemantics

namespace StandardECDSA

open StandardECDSA.Gadgets
open StandardECDSA.Phases
open StandardECDSA.Math

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

/-! ## Circuit stages

`main` is written as an explicit lambda over named stages so that its
`operations` list can be split syntactically (`main_ops`) without asking the
elaborator to `whnf` the whole `do` block.  Each stage is itself an explicit
lambda with an `_ops` equation lemma.
-/

/-- The seed read by the circuit: `(ry, hx, hy, overflow)`. -/
structure Seed where
  /-- The `y`-coordinate of the signature point `R`. -/
  ry : E
  /-- The `x`-coordinate of the offset point `H`. -/
  hx : E
  /-- The `y`-coordinate of the offset point `H`. -/
  hy : E
  /-- The Boolean selecting `R.x = r + n·overflow`. -/
  overflow : E

/-- The three 256-bit hint vectors `(eBit, rBit, tBit)`. -/
structure Bits where
  /-- The 256 digest bits. -/
  eb : Vector E 256
  /-- The 256 bits of `r`. -/
  rb : Vector E 256
  /-- The 256 bits of `t = n - s`. -/
  sb : Vector E 256

/-- Stage 1: read the four seed hints and assert `overflow` Boolean. -/
def seedPhase (inp : Var Input Fp) : C Seed := fun n =>
  let o0 := (hint 0 n).2
  let o1 := (hint 1 (n + Operations.localLength o0)).2
  let o2 := (hint 2 (n + Operations.localLength o0 + Operations.localLength o1)).2
  let o3 := (hint 3 (n + Operations.localLength o0 + Operations.localLength o1
    + Operations.localLength o2)).2
  let o4 := (Gadgets.assertBool (hint 3 (n + Operations.localLength o0
    + Operations.localLength o1 + Operations.localLength o2)).1
    (n + Operations.localLength o0 + Operations.localLength o1
      + Operations.localLength o2 + Operations.localLength o3)).2
  (⟨(hint 0 n).1, (hint 1 (n + Operations.localLength o0)).1,
    (hint 2 (n + Operations.localLength o0 + Operations.localLength o1)).1,
    (hint 3 (n + Operations.localLength o0 + Operations.localLength o1
      + Operations.localLength o2)).1⟩,
   o0 ++ o1 ++ o2 ++ o3 ++ o4)

/-- Stage 2: the three on-curve assertions. -/
def curvePhase (inp : Var Input Fp) (s : Seed) : C Unit := fun n =>
  let o0 := (isOnCurve inp.pkX inp.pkY n).2
  let o1 := (isOnCurve (inp.r + sc nFp s.overflow) s.ry
    (n + Operations.localLength o0)).2
  let o2 := (isOnCurve s.hx s.hy
    (n + Operations.localLength o0 + Operations.localLength o1)).2
  ((), o0 ++ o1 ++ o2)

/-- Stage 3: the two nonzero assertions (`r` and `t = n - s`). -/
def nonzeroPhase (inp : Var Input Fp) : C Unit := fun n =>
  let o0 := (nonzero inp.r n).2
  let o1 := (nonzero (cst (Challenge.Specs.ECDSAP256.n : Fp) - inp.s)
    (n + Operations.localLength o0)).2
  ((), o0 ++ o1)

/-- Stage 4: the three 256-bit hint vectors. -/
def bitsPhase : C Bits := fun n =>
  let o0 := (bitVec 4 3 n).2
  let o1 := (bitVec 5 3 (n + Operations.localLength o0)).2
  let o2 := (bitVec 6 3 (n + Operations.localLength o0 + Operations.localLength o1)).2
  (⟨(bitVec 4 3 n).1, (bitVec 5 3 (n + Operations.localLength o0)).1,
    (bitVec 6 3 (n + Operations.localLength o0 + Operations.localLength o1)).1⟩,
   o0 ++ o1 ++ o2)

/-- Stage 5: the two digest-limb bindings and the two scalar bindings. -/
def bindPhase (inp : Var Input Fp) (b : Bits) : C Unit := fun n =>
  let o0 := (Circuit.assertZero (linComb b.eb 0 128 - inp.digestLo) n).2
  let o1 := (Circuit.assertZero (linComb b.eb 128 128 - inp.digestHi) n).2
  let o2 := (Circuit.assertZero (linComb b.rb 0 256 - inp.r) n).2
  let o3 := (Circuit.assertZero (linComb b.sb 0 256
    - (cst (Challenge.Specs.ECDSAP256.n : Fp) - inp.s)) n).2
  ((), o0 ++ o1 ++ o2 ++ o3)

/-- Stage 6: the two order comparisons and the guarded lift comparison. -/
def cmpPhase (b : Bits) (overflow : E) : C Unit := fun n =>
  let o0 := (assertLtOrderOf nSubOne (fun i => b.rb.getD i (cst 0)) n).2
  let o1 := (assertLtOrderOf nSubOne (fun i => b.sb.getD i (cst 0))
    (n + Operations.localLength o0)).2
  let o2 := (assertLtOrderGuardedOf pSubNSubOne overflow
    (fun i => b.rb.getD i (cst 0))
    (n + Operations.localLength o0 + Operations.localLength o1)).2
  ((), o0 ++ o1 ++ o2)

/-- The standard P-256 ECDSA circuit. -/
def main (inp : Var Input Fp) : C Unit := fun n =>
  let s := seedPhase inp n
  let n1 := n + Operations.localLength s.2
  let c := curvePhase inp s.1 n1
  let n2 := n1 + Operations.localLength c.2
  let z := nonzeroPhase inp n2
  let n3 := n2 + Operations.localLength z.2
  let b := bitsPhase n3
  let n4 := n3 + Operations.localLength b.2
  let d := bindPhase inp b.1 n4
  let n5 := n4 + Operations.localLength d.2
  let m := cmpPhase b.1 s.1.overflow n5
  let n6 := n5 + Operations.localLength m.2
  let ep := fixedBase (s.1.hx, s.1.hy) b.1.eb n6
  let n7 := n6 + Operations.localLength ep.2
  let tb := shiftedTables (s.1.hx, s.1.hy) (inp.pkX, inp.pkY)
    (inp.r + sc nFp s.1.overflow, s.1.ry) n7
  let n8 := n7 + Operations.localLength tb.2
  let ld := jointLadder (s.1.hx, -s.1.hy) tb.1 b.1.rb b.1.sb (ep.1.1, -ep.1.2) n8
  ((), s.2 ++ c.2 ++ z.2 ++ b.2 ++ d.2 ++ m.2 ++ ep.2 ++ tb.2 ++ ld.2)

/-! ## Expression evaluation helpers

`Expression.eval` is a structural recursion, so `simp only [Expression.eval]` does
not fire on terms whose head is the `HAdd`/`HSub`/`Neg` projection rather than the
`Expression` constructor.  These lemmas state the evaluation of each constructor
directly, which makes `simp only [eval_var, eval_const, eval_add, eval_mul,
eval_neg, eval_sub]` a complete evaluator for affine expressions.
-/

@[simp] theorem eval_var (env : Environment Fp) (i : Nat) :
    Expression.eval env (var ⟨i⟩) = env.get i := rfl

@[simp] theorem eval_const (env : Environment Fp) (c : Fp) :
    Expression.eval env (Expression.const c) = c := rfl

@[simp] theorem eval_add (env : Environment Fp) (a b : E) :
    Expression.eval env (Expression.add a b) = Expression.eval env a + Expression.eval env b :=
  rfl

@[simp] theorem eval_mul (env : Environment Fp) (a b : E) :
    Expression.eval env (Expression.mul a b) = Expression.eval env a * Expression.eval env b :=
  rfl

@[simp] theorem eval_neg (env : Environment Fp) (a : E) :
    Expression.eval env (-a) = - Expression.eval env a := by
  show Expression.eval env (Expression.mul (Expression.const (-1)) a) = - Expression.eval env a
  rw [eval_mul, eval_const, neg_one_mul]

@[simp] theorem eval_sub (env : Environment Fp) (a b : E) :
    Expression.eval env (a - b) = Expression.eval env a - Expression.eval env b := by
  show Expression.eval env (Expression.add a (Expression.mul (Expression.const (-1)) b))
    = Expression.eval env a - Expression.eval env b
  rw [eval_add, eval_mul, eval_const, neg_one_mul, sub_eq_add_neg]

@[simp] theorem eval_cst (env : Environment Fp) (c : Fp) :
    Expression.eval env (cst c) = c := rfl

@[simp] theorem eval_sc (env : Environment Fp) (c : Fp) (e : E) :
    Expression.eval env (sc c e) = c * Expression.eval env e := rfl

/-- `Vector.getD` at an in-range index is `Vector.get`. -/
theorem getD_eq_get {v : Vector E 256} {k : Nat} (hk : k < 256) :
    v.getD k (cst 0) = v.get ⟨k, hk⟩ := by
  simp only [Vector.getD, Vector.get, Array.getD, v.size_toArray, hk, dif_pos, Fin.val_cast]
  rfl

/-! ## Field-level gadget soundness -/

/-- `assertBool` forces its argument to be Boolean. -/
theorem assertBool_sound (b : E) (env : Environment Fp) (n : Nat)
    (hc : ConstraintsHold.Soundness env ((Gadgets.assertBool b).operations n)) :
    Expression.eval env b = 0 ∨ Expression.eval env b = 1 := by
  have h : env (.mul b b - b) = 0 := by
    simpa only [ConstraintsHold.Soundness, Gadgets.assertBool, Circuit.assertZero,
      Circuit.operations, Operations.forAllNoOffset, true_and] using hc.1
  refine (bool_iff' _).mp ?_
  simpa only [eval_var, eval_const, eval_add, eval_mul, eval_neg, eval_sub,
    neg_one_mul] using h

/-- The operations of `nonzero`. -/
theorem nonzero_ops (x : E) (n : Nat) :
    (nonzero x).operations n
      = [.witness 1 (.ofFExpr (.inv (.expr x))), .assert (pm x (var ⟨n⟩) - cst 1)] := by
  simp only [nonzero, Circuit.operations, bind_snd, pure_snd, Circuit.witnessField,
    Circuit.assertZero, Operations.localLength, List.cons_append, List.nil_append]

/-- `nonzero` forces its argument to be nonzero. -/
theorem nonzero_sound (x : E) (env : Environment Fp) (n : Nat)
    (hc : ConstraintsHold.Soundness env ((nonzero x).operations n)) :
    Expression.eval env x ≠ 0 := by
  rw [nonzero_ops] at hc
  simp only [ConstraintsHold.Soundness, Operations.forAllNoOffset, true_and] at hc
  refine nonzero_spec (inv := env.get n) ?_
  simpa only [eval_var, eval_const, eval_add, eval_mul, eval_neg, eval_sub, pm, cst,
    neg_one_mul, mul_one] using hc.1

/-- `isOnCurve` forces its arguments to be an affine on-curve point. -/
theorem isOnCurve_sound (x y : E) (env : Environment Fp) (n : Nat)
    (hc : ConstraintsHold.Soundness env ((isOnCurve x y).operations n)) :
    NS (Expression.eval env x) (Expression.eval env y) := by
  simp only [ConstraintsHold.Soundness, isOnCurve, mm, bind_snd] at hc
  rw [Operations.forAllNoOffset_append] at hc
  obtain ⟨h1, h2⟩ := hc
  have h1a := forAllNoOffset_constraints _ h1
    (by intro s hs; rw [mat_subcircuits] at hs; simp at hs)
  have h2a := forAllNoOffset_constraints _ h2
    (by intro s hs; rw [assertZeroLazy_subcircuits] at hs; simp at hs)
  have hmat : Expression.eval env ((mat (.mul x x) n).1)
      = Expression.eval env x * Expression.eval env x := by
    rw [mat_output_eq]
    exact matOut_eval env _ n (by rwa [mat_operations_eq] at h1a)
  have hz := azl_eval env (Expression.mul y y -
    (Expression.mul x ((mat (Expression.mul x x) n).1) + sc pa x + cst pb)) _ h2a
  simp only [circuit_norm, hmat, sc, cst, pa, pb] at hz
  have hpa : params.a = pa := rfl
  have hpb : params.b = pb := rfl
  refine StandardECDSA.Math.AffineBridge.short_nonsingular params
    (Expression.eval env x) (Expression.eval env y) ?_
  rw [hpa, hpb]
  simp only [pa, pb]
  linear_combination hz

/-! ## The 256-bit hint vectors -/

/-- The operations of one bit body. -/
theorem bitBody_ops (base stride : Nat) (i : Fin 256) (n : Nat) :
    (bitBody base stride i).operations n
      = (hint (base + stride * i.val)).operations n
        ++ (Gadgets.assertBool ((hint (base + stride * i.val)).output n)).operations (n + 1) := by
  simp only [bitBody, Circuit.operations, Circuit.output, bind_snd, pure_snd, hint,
    witnessField, Circuit.localLength, Operations.append_localLength, Operations.localLength,
    Nat.add_zero, List.append_nil]

/-- The output of one bit body is the hint wire. -/
theorem bitBody_out (base stride : Nat) (i : Fin 256) (n : Nat) :
    (bitBody base stride i).output n = (hint (base + stride * i.val)).output n := by
  simp only [bitBody, output_bind, output_pure, output_witnessField, hint, witnessField,
    Circuit.operations, Circuit.localLength, Operations.append_localLength,
    Operations.localLength]

/-- A `bitVec` allocates 256 wires. -/
theorem bitBody_localLength (base stride : Nat) : (bitBody base stride 0).localLength = 1 := by
  simp only [bitBody, hint, witnessField, Gadgets.assertBool, Circuit.assertZero,
    Circuit.localLength, bind_snd, pure_snd, Operations.append_localLength,
    Operations.localLength]

/-- A `bitVec` allocates 256 wires. -/
theorem bitVec_localLength (base stride n : Nat) : (bitVec base stride).localLength n = 256 := by
  rw [bitVec, Circuit.mapFinRange.localLength_eq, bitBody_localLength, Nat.mul_one]

/-- The `k`-th entry of a `bitVec` output is the wire `n + k`. -/
theorem bitVec_out (base stride n : Nat) (k : Fin 256) :
    ((bitVec base stride).output n).get k = var ⟨n + k.val⟩ := by
  rw [bitVec, Circuit.mapFinRange.output_eq]
  simp only [Vector.getElem_mapFinRange, Vector.get_eq_getElem]
  rw [bitBody_localLength, Nat.mul_one]
  simp only [bitBody_out, hint, witnessField, Circuit.output]

/-- Every entry of a `bitVec` is Boolean. -/
theorem bitVec_sound (base stride n : Nat) (env : Environment Fp)
    (hc : ConstraintsHold.Soundness env ((bitVec base stride).operations n)) :
    ∀ k : Fin 256, Expression.eval env (((bitVec base stride).output n).get k) = 0 ∨
      Expression.eval env (((bitVec base stride).output n).get k) = 1 := by
  intro k
  simp only [ConstraintsHold.Soundness] at hc
  rw [bitVec, Circuit.mapFinRange] at hc
  have hsplit := (Circuit.MapM.mapFinRangeM_forAllNoOffset_iff
    (circuit := bitBody base stride) (constant := bitBody_constantLength base stride)).mp hc
  have hk := hsplit k
  rw [show (bitBody_constantLength base stride).localLength = 1 from rfl, Nat.mul_one] at hk
  rw [bitBody_ops] at hk
  rw [Operations.forAllNoOffset_append] at hk
  obtain ⟨-, hk⟩ := hk
  have hb := assertBool_sound _ env _ hk
  rw [bitVec_out]
  simpa only [eval_var, hint, witnessField, Circuit.output] using hb

/-! ## Stage soundness

Each stage is exposed with an `_ops` equation lemma that only unfolds the stage's
own `let` structure, keeping the gadget `.operations` opaque.  This keeps the
terms small enough for the elaborator and lets the soundness proofs split the
constraint list with `Operations.forAllNoOffset_append` and hand each component
to the corresponding gadget spec.
-/

/-- The output of the seed stage. -/
theorem seedPhase_out (inp : Var Input Fp) (n : Nat) :
    (seedPhase inp).output n
      = ⟨(hint 0).output n, (hint 1).output (n + 1), (hint 2).output (n + 2),
          (hint 3).output (n + 3)⟩ := by
  simp only [seedPhase, Circuit.output, hint, witnessField, Circuit.localLength,
    Operations.append_localLength, Operations.localLength]

/-- The operations of the seed stage. -/
theorem seedPhase_ops (inp : Var Input Fp) (n : Nat) :
    (seedPhase inp).operations n
      = (hint 0).operations n ++ (hint 1).operations (n + 1)
        ++ (hint 2).operations (n + 2) ++ (hint 3).operations (n + 3)
        ++ (Gadgets.assertBool ((hint 3).output (n + 3))).operations (n + 4) := by
  simp only [seedPhase, Circuit.operations, Circuit.output, hint, witnessField,
    Circuit.localLength, Operations.append_localLength, Operations.localLength]

/-- The seed stage forces `overflow` to be Boolean. -/
theorem seedPhase_sound (inp : Var Input Fp) (env : Environment Fp) (n : Nat)
    (hc : ConstraintsHold.Soundness env ((seedPhase inp).operations n)) :
    Expression.eval env ((seedPhase inp).output n).overflow = 0 ∨
      Expression.eval env ((seedPhase inp).output n).overflow = 1 := by
  rw [seedPhase_out]
  simp only [hint, witnessField, Circuit.output]
  rw [seedPhase_ops] at hc
  simp only [ConstraintsHold.Soundness, Operations.forAllNoOffset_append, and_assoc] at hc
  obtain ⟨-, -, -, -, hb⟩ := hc
  simp only [Gadgets.assertBool, Circuit.assertZero, Circuit.operations,
    Operations.forAllNoOffset, true_and, and_true, hint, witnessField, Circuit.output] at hb
  refine (bool_iff' _).mp ?_
  simpa only [eval_var, eval_const, eval_add, eval_mul, eval_neg, eval_sub,
    neg_one_mul] using hb

/-- The operations of the curve stage. -/
theorem curvePhase_ops (inp : Var Input Fp) (s : Seed) (n : Nat) :
    (curvePhase inp s).operations n
      = (isOnCurve inp.pkX inp.pkY).operations n
        ++ (isOnCurve (inp.r + sc nFp s.overflow) s.ry).operations
             (n + Operations.localLength (isOnCurve inp.pkX inp.pkY n).2)
        ++ (isOnCurve s.hx s.hy).operations
             (n + Operations.localLength (isOnCurve inp.pkX inp.pkY n).2
                + Operations.localLength (isOnCurve (inp.r + sc nFp s.overflow) s.ry
                    (n + Operations.localLength (isOnCurve inp.pkX inp.pkY n).2)).2) := by
  simp only [curvePhase, Circuit.operations]

/-- The curve stage forces the three points to be on the curve. -/
theorem curvePhase_sound (inp : Var Input Fp) (s : Seed) (env : Environment Fp) (n : Nat)
    (hc : ConstraintsHold.Soundness env ((curvePhase inp s).operations n)) :
    NS (Expression.eval env inp.pkX) (Expression.eval env inp.pkY) ∧
      NS (Expression.eval env (inp.r + sc nFp s.overflow)) (Expression.eval env s.ry) ∧
      NS (Expression.eval env s.hx) (Expression.eval env s.hy) := by
  rw [curvePhase_ops] at hc
  simp only [ConstraintsHold.Soundness, Operations.forAllNoOffset_append, and_assoc] at hc
  obtain ⟨h1, h2, h3⟩ := hc
  exact ⟨isOnCurve_sound _ _ env _ h1, isOnCurve_sound _ _ env _ h2,
    isOnCurve_sound _ _ env _ h3⟩

/-- The operations of the nonzero stage. -/
theorem nonzeroPhase_ops (inp : Var Input Fp) (n : Nat) :
    (nonzeroPhase inp).operations n
      = (nonzero inp.r).operations n
        ++ (nonzero (cst (Challenge.Specs.ECDSAP256.n : Fp) - inp.s)).operations
             (n + Operations.localLength (nonzero inp.r n).2) := by
  simp only [nonzeroPhase, Circuit.operations]

/-- The nonzero stage forces `r` and `n - s` to be nonzero. -/
theorem nonzeroPhase_sound (inp : Var Input Fp) (env : Environment Fp) (n : Nat)
    (hc : ConstraintsHold.Soundness env ((nonzeroPhase inp).operations n)) :
    Expression.eval env inp.r ≠ 0 ∧
      Expression.eval env (cst (Challenge.Specs.ECDSAP256.n : Fp) - inp.s) ≠ 0 := by
  rw [nonzeroPhase_ops] at hc
  simp only [ConstraintsHold.Soundness, Operations.forAllNoOffset_append, and_assoc] at hc
  obtain ⟨h1, h2⟩ := hc
  exact ⟨nonzero_sound _ env _ h1, nonzero_sound _ env _ h2⟩

/-- The output of the bits stage. -/
theorem bitsPhase_out (n : Nat) :
    (bitsPhase).output n
      = ⟨(bitVec 4 3).output n, (bitVec 5 3).output (n + 256),
          (bitVec 6 3).output (n + 512)⟩ := by
  simp only [bitsPhase, Circuit.output, Circuit.localLength, bitVec_localLength]

/-- The operations of the bits stage. -/
theorem bitsPhase_ops (n : Nat) :
    (bitsPhase).operations n
      = (bitVec 4 3).operations n ++ (bitVec 5 3).operations (n + 256)
        ++ (bitVec 6 3).operations (n + 512) := by
  simp only [bitsPhase, Circuit.operations, Circuit.localLength, bitVec_localLength]

/-- The bits stage forces all 768 hint bits to be Boolean. -/
theorem bitsPhase_sound (env : Environment Fp) (n : Nat)
    (hc : ConstraintsHold.Soundness env ((bitsPhase).operations n)) :
    (∀ k : Fin 256, Expression.eval env (((bitsPhase).output n).eb.get k) = 0 ∨
        Expression.eval env (((bitsPhase).output n).eb.get k) = 1) ∧
      (∀ k : Fin 256, Expression.eval env (((bitsPhase).output n).rb.get k) = 0 ∨
        Expression.eval env (((bitsPhase).output n).rb.get k) = 1) ∧
      (∀ k : Fin 256, Expression.eval env (((bitsPhase).output n).sb.get k) = 0 ∨
        Expression.eval env (((bitsPhase).output n).sb.get k) = 1) := by
  rw [bitsPhase_ops] at hc
  simp only [ConstraintsHold.Soundness, Operations.forAllNoOffset_append, and_assoc] at hc
  obtain ⟨h1, h2, h3⟩ := hc
  rw [bitsPhase_out]
  refine ⟨?_, ?_, ?_⟩
  · intro k; exact bitVec_sound 4 3 n env h1 k
  · intro k; exact bitVec_sound 5 3 (n + 256) env h2 k
  · intro k; exact bitVec_sound 6 3 (n + 512) env h3 k

/-- The operations of the binding stage. -/
theorem bindPhase_ops (inp : Var Input Fp) (b : Bits) (n : Nat) :
    (bindPhase inp b).operations n
      = [.assert (linComb b.eb 0 128 - inp.digestLo),
          .assert (linComb b.eb 128 128 - inp.digestHi),
          .assert (linComb b.rb 0 256 - inp.r),
          .assert (linComb b.sb 0 256 - (cst (Challenge.Specs.ECDSAP256.n : Fp) - inp.s))] := by
  simp only [bindPhase, Circuit.operations, Circuit.assertZero, Operations.localLength,
    List.cons_append, List.nil_append]

/-- The binding stage forces the four linear-combination equalities. -/
theorem bindPhase_sound (inp : Var Input Fp) (b : Bits) (env : Environment Fp) (n : Nat)
    (hc : ConstraintsHold.Soundness env ((bindPhase inp b).operations n)) :
    Expression.eval env (linComb b.eb 0 128) = Expression.eval env inp.digestLo ∧
      Expression.eval env (linComb b.eb 128 128) = Expression.eval env inp.digestHi ∧
      Expression.eval env (linComb b.rb 0 256) = Expression.eval env inp.r ∧
      Expression.eval env (linComb b.sb 0 256)
        = Expression.eval env (cst (Challenge.Specs.ECDSAP256.n : Fp) - inp.s) := by
  rw [bindPhase_ops] at hc
  simp only [ConstraintsHold.Soundness, Operations.forAllNoOffset, true_and, and_true] at hc
  obtain ⟨h1, h2, h3, h4⟩ := hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eval_sub] at h1; exact sub_eq_zero.mp h1
  · rw [eval_sub] at h2; exact sub_eq_zero.mp h2
  · rw [eval_sub] at h3; exact sub_eq_zero.mp h3
  · rw [eval_sub] at h4; exact sub_eq_zero.mp h4

/-- `ConstraintsHold.Soundness` splits over `++`.  Stated with the two lists as
variables so that `List.append` stays stuck and `forAllNoOffset_append` applies
without unfolding either side. -/
theorem soundness_append {env : Environment Fp} {a b : Operations Fp}
    (h : ConstraintsHold.Soundness env (a ++ b)) :
    ConstraintsHold.Soundness env a ∧ ConstraintsHold.Soundness env b := by
  simpa only [ConstraintsHold.Soundness, Operations.forAllNoOffset_append] using h

/-- Three-way version of `soundness_append`. -/
theorem soundness_append3 {env : Environment Fp} {a b c : Operations Fp}
    (h : ConstraintsHold.Soundness env (a ++ b ++ c)) :
    ConstraintsHold.Soundness env a ∧ ConstraintsHold.Soundness env b ∧
      ConstraintsHold.Soundness env c := by
  simpa only [ConstraintsHold.Soundness, Operations.forAllNoOffset_append, and_assoc] using h

/-- The operations of the comparison stage. -/
theorem cmpPhase_ops (b : Bits) (overflow : E) (n : Nat) :
    (cmpPhase b overflow).operations n
      = (assertLtOrderOf nSubOne (fun i => b.rb.getD i (cst 0))).operations n
        ++ (assertLtOrderOf nSubOne (fun i => b.sb.getD i (cst 0))).operations
             (n + Operations.localLength
               (assertLtOrderOf nSubOne (fun i => b.rb.getD i (cst 0)) n).2)
        ++ (assertLtOrderGuardedOf pSubNSubOne overflow
              (fun i => b.rb.getD i (cst 0))).operations
             (n + Operations.localLength
                (assertLtOrderOf nSubOne (fun i => b.rb.getD i (cst 0)) n).2
                + Operations.localLength
                  (assertLtOrderOf nSubOne (fun i => b.sb.getD i (cst 0))
                    (n + Operations.localLength
                      (assertLtOrderOf nSubOne (fun i => b.rb.getD i (cst 0)) n).2)).2) :=
  rfl

set_option linter.constructorNameAsVariable false in
/-- The comparison stage forces the three order bounds. -/
theorem cmpPhase_sound (b : Bits) (overflow : E) (env : Environment Fp) (n : Nat)
    (hb : ∀ k : Fin 256, Expression.eval env (b.rb.get k) = 0 ∨
      Expression.eval env (b.rb.get k) = 1)
    (hb' : ∀ k : Fin 256, Expression.eval env (b.sb.get k) = 0 ∨
      Expression.eval env (b.sb.get k) = 1)
    (hc : ConstraintsHold.Soundness env ((cmpPhase b overflow).operations n)) :
    prefVal (fun j => aNatOf (fun k => Expression.eval env (b.rb.getD k (cst 0))) (255 - j)) 256
        ≤ nSubOne ∧
      prefVal (fun j => aNatOf (fun k => Expression.eval env (b.sb.getD k (cst 0))) (255 - j)) 256
        ≤ nSubOne ∧
      (Expression.eval env overflow = 1 →
        prefVal (fun j => aNatOf (fun k => Expression.eval env (b.rb.getD k (cst 0))) (255 - j)) 256
          ≤ pSubNSubOne) := by
  rw [cmpPhase_ops] at hc
  obtain ⟨h1, h2, h3⟩ := soundness_append3 hc
  have hbool : ∀ k < 256, Expression.eval env (b.rb.getD k (cst 0)) = 0 ∨
      Expression.eval env (b.rb.getD k (cst 0)) = 1 := by
    intro k hk
    rw [getD_eq_get hk]
    exact hb ⟨k, hk⟩
  have hbool' : ∀ k < 256, Expression.eval env (b.sb.getD k (cst 0)) = 0 ∨
      Expression.eval env (b.sb.getD k (cst 0)) = 1 := by
    intro k hk
    rw [getD_eq_get hk]
    exact hb' ⟨k, hk⟩
  refine ⟨?_, ?_, ?_⟩
  · exact assertLtOrderOf_sound _ (fun i => b.rb.getD i (cst 0)) env n h1 hbool
      prefVal_boundNat_n runsCover_n
  · exact assertLtOrderOf_sound _ (fun i => b.sb.getD i (cst 0)) env
      (n + Operations.localLength
        (assertLtOrderOf nSubOne (fun i => b.rb.getD i (cst 0)) n).2)
      h2 hbool' prefVal_boundNat_n runsCover_n
  · intro hg
    exact assertLtOrderGuardedOf_sound _ overflow (fun i => b.rb.getD i (cst 0)) env
      (n + Operations.localLength
          (assertLtOrderOf nSubOne (fun i => b.rb.getD i (cst 0)) n).2
        + Operations.localLength
          (assertLtOrderOf nSubOne (fun i => b.sb.getD i (cst 0))
            (n + Operations.localLength
              (assertLtOrderOf nSubOne (fun i => b.rb.getD i (cst 0)) n).2)).2)
      h3 hg hbool prefVal_boundNat_pn runsCover_pn


/-! ## Splitting the assembled circuit

`main` is a nine-stage append.  The equation lemma below exposes that shape
syntactically, so that soundness can be split without asking the elaborator to
`whnf` the whole circuit. -/

/-- The operations of `main`, as a nine-way append. -/
theorem main_ops (inp : Var Input Fp) (n : Nat) :
    (main inp).operations n =
      (let s := seedPhase inp n
       let n1 := n + Operations.localLength s.2
       let c := curvePhase inp s.1 n1
       let n2 := n1 + Operations.localLength c.2
       let z := nonzeroPhase inp n2
       let n3 := n2 + Operations.localLength z.2
       let b := bitsPhase n3
       let n4 := n3 + Operations.localLength b.2
       let d := bindPhase inp b.1 n4
       let n5 := n4 + Operations.localLength d.2
       let m := cmpPhase b.1 s.1.overflow n5
       let n6 := n5 + Operations.localLength m.2
       let ep := fixedBase (s.1.hx, s.1.hy) b.1.eb n6
       let n7 := n6 + Operations.localLength ep.2
       let tb := shiftedTables (s.1.hx, s.1.hy) (inp.pkX, inp.pkY)
         (inp.r + sc nFp s.1.overflow, s.1.ry) n7
       let n8 := n7 + Operations.localLength tb.2
       let ld := jointLadder (s.1.hx, -s.1.hy) tb.1 b.1.rb b.1.sb (ep.1.1, -ep.1.2) n8
       s.2 ++ c.2 ++ z.2 ++ b.2 ++ d.2 ++ m.2 ++ ep.2 ++ tb.2 ++ ld.2) := rfl

set_option linter.constructorNameAsVariable false in
/-- Nine-way version of `soundness_append`. -/
theorem soundness_append9 {env : Environment Fp} {a b c d e f g h i : Operations Fp}
    (hc : ConstraintsHold.Soundness env (a ++ b ++ c ++ d ++ e ++ f ++ g ++ h ++ i)) :
    ConstraintsHold.Soundness env a ∧ ConstraintsHold.Soundness env b ∧
      ConstraintsHold.Soundness env c ∧ ConstraintsHold.Soundness env d ∧
      ConstraintsHold.Soundness env e ∧ ConstraintsHold.Soundness env f ∧
      ConstraintsHold.Soundness env g ∧ ConstraintsHold.Soundness env h ∧
      ConstraintsHold.Soundness env i := by
  simpa only [ConstraintsHold.Soundness, Operations.forAllNoOffset_append, and_assoc] using hc

@[simp] theorem eval_add' (env : Environment Fp) (a b : E) :
    Expression.eval env (a + b) = Expression.eval env a + Expression.eval env b := rfl

@[simp] theorem eval_sc' (env : Environment Fp) (c : Fp) (e : E) :
    Expression.eval env (sc c e) = c * Expression.eval env e := rfl

theorem eval_linComb (env : Environment Fp) (v : Vector E 256) (lo len : Nat) :
    Expression.eval env (linComb v lo len)
      = leSum (fun i : Fin len => Expression.eval env (v.getD (lo + i.val) (cst 0))) := by
  induction len with
  | zero => simp only [linComb, List.range_zero, List.foldl_nil, eval_cst, leSum,
      Fin.sum_univ_zero]
  | succ k ih =>
    have hr : List.range (k + 1) = List.range k ++ [k] := List.range_succ
    rw [linComb, hr, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [show (List.range k).foldl
        (fun acc j => acc + sc ((2 : Fp) ^ j) (v.getD (lo + j) (cst 0))) (cst 0)
        = linComb v lo k from rfl]
    simp only [eval_add', eval_sc']
    rw [ih]
    simp only [leSum, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

theorem prefVal_eq_sum (x : Nat → Nat) : ∀ k : Nat,
    prefVal x k = ∑ j ∈ Finset.range k, 2 ^ (k - 1 - j) * x j
  | 0 => by simp [prefVal]
  | k + 1 => by
    rw [prefVal, prefVal_eq_sum x k, Finset.sum_range_succ]
    rw [Finset.mul_sum]
    have hlast : 2 ^ (k + 1 - 1 - k) * x k = x k := by
      rw [show k + 1 - 1 - k = 0 from by omega, pow_zero, one_mul]
    rw [hlast]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.mem_range] at hj
    rw [show k + 1 - 1 - j = (k - 1 - j) + 1 from by omega, pow_succ]
    ring

theorem prefVal_rev (f : Fin 256 → Nat) :
    prefVal (fun j => f ⟨255 - j, by omega⟩) 256 = leNat f := by
  rw [prefVal_eq_sum, leNat_eq_sum_range]
  have h : ∀ j ∈ Finset.range 256,
      2 ^ (256 - 1 - j) * f ⟨255 - j, by omega⟩
        = (fun i => 2 ^ i * f ⟨i % 256, Nat.mod_lt _ (by norm_num)⟩) (256 - 1 - j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    simp only [Nat.mod_eq_of_lt (by omega : 256 - 1 - j < 256)]
  rw [Finset.sum_congr rfl h]
  exact Finset.sum_range_reflect
    (fun i => 2 ^ i * f ⟨i % 256, Nat.mod_lt _ (by norm_num)⟩) 256

theorem leNat_split {m n : Nat} (f : Fin (m + n) → Nat) :
    leNat f = leNat (fun i : Fin m => f ⟨i.val, by omega⟩)
      + 2 ^ m * leNat (fun i : Fin n => f ⟨m + i.val, by omega⟩) := by
  unfold leNat
  rw [Fin.sum_univ_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  show 2 ^ (m + (i : Nat)) * f ⟨m + (i : Nat), _⟩
    = 2 ^ m * (2 ^ (i : Nat) * f ⟨m + (i : Nat), _⟩)
  rw [pow_add]
  ring

theorem two_pow_128_le_p : 2 ^ 128 ≤ p := by decide

theorem leNat_congr {k : Nat} {f g : Fin k → Nat} (h : ∀ i, f i = g i) :
    leNat f = leNat g := by
  unfold leNat
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

/-- The 256 digest bits recompose to the two-limb digest. -/
theorem leNat_eb_eq_digest (env : Environment Fp) (inp : Var Input Fp) (b : Bits)
    (hlo : Expression.eval env (linComb b.eb 0 128) = Expression.eval env inp.digestLo)
    (hhi : Expression.eval env (linComb b.eb 128 128) = Expression.eval env inp.digestHi)
    (hb : ∀ k : Fin 256, Expression.eval env (b.eb.get k) = 0 ∨
      Expression.eval env (b.eb.get k) = 1) :
    leNat (fun i : Fin 256 => (Expression.eval env (b.eb.get i)).val)
      = (Digest.mk (Expression.eval env inp.digestLo)
          (Expression.eval env inp.digestHi)).toNat := by
  have hget : ∀ (i : Nat) (hi : i < 256), b.eb.getD i (cst 0) = b.eb.get ⟨i, hi⟩ :=
    fun i hi => getD_eq_get hi
  have hlt : ∀ (v : Fin 128 → Fp),
      (∀ i, v i = 0 ∨ v i = 1) → leNat (fun i => (v i).val) < p := by
    intro v hv
    have : Fact (1 < p) := ⟨by decide⟩
    refine lt_of_lt_of_le (leNat_lt _ (fun i => ?_)) two_pow_128_le_p
    rcases hv i with h | h
    · rw [h]; exact Nat.zero_le 1
    · rw [h, ZMod.val_one p]
  have hlow : leNat (fun i : Fin 128 => (Expression.eval env (b.eb.get ⟨i.val, by omega⟩)).val)
      = (Expression.eval env inp.digestLo).val := by
    have hv : ∀ i : Fin 128, Expression.eval env (b.eb.getD (0 + i.val) (cst 0)) = 0 ∨
        Expression.eval env (b.eb.getD (0 + i.val) (cst 0)) = 1 := by
      intro i
      rw [Nat.zero_add, hget i.val (by omega)]
      exact hb _
    have h1 : leSum (fun i : Fin 128 => Expression.eval env (b.eb.getD (0 + i.val) (cst 0)))
        = Expression.eval env inp.digestLo := by
      rw [← eval_linComb]; exact hlo
    have h2 : (leSum (fun i : Fin 128 =>
        Expression.eval env (b.eb.getD (0 + i.val) (cst 0)))).val
        = leNat (fun i : Fin 128 =>
            (Expression.eval env (b.eb.getD (0 + i.val) (cst 0))).val) :=
      val_leSum' _ hv (hlt _ hv)
    have h3 : leNat (fun i : Fin 128 => (Expression.eval env (b.eb.get ⟨i.val, by omega⟩)).val)
        = leNat (fun i : Fin 128 =>
            (Expression.eval env (b.eb.getD (0 + i.val) (cst 0))).val) :=
      leNat_congr fun i => by rw [Nat.zero_add, hget i.val (by omega)]
    rw [h3, ← h2, h1]
  have hhigh : leNat (fun i : Fin 128 => (Expression.eval env (b.eb.get ⟨128 + i.val, by omega⟩)).val)
      = (Expression.eval env inp.digestHi).val := by
    have hv : ∀ i : Fin 128, Expression.eval env (b.eb.getD (128 + i.val) (cst 0)) = 0 ∨
        Expression.eval env (b.eb.getD (128 + i.val) (cst 0)) = 1 := by
      intro i
      rw [hget (128 + i.val) (by omega)]
      exact hb _
    have h1 : leSum (fun i : Fin 128 => Expression.eval env (b.eb.getD (128 + i.val) (cst 0)))
        = Expression.eval env inp.digestHi := by
      rw [← eval_linComb]; exact hhi
    have h2 : (leSum (fun i : Fin 128 =>
        Expression.eval env (b.eb.getD (128 + i.val) (cst 0)))).val
        = leNat (fun i : Fin 128 =>
            (Expression.eval env (b.eb.getD (128 + i.val) (cst 0))).val) :=
      val_leSum' _ hv (hlt _ hv)
    have h3 : leNat (fun i : Fin 128 => (Expression.eval env (b.eb.get ⟨128 + i.val, by omega⟩)).val)
        = leNat (fun i : Fin 128 =>
            (Expression.eval env (b.eb.getD (128 + i.val) (cst 0))).val) :=
      leNat_congr fun i => by rw [hget (128 + i.val) (by omega)]
    rw [h3, ← h2, h1]
  rw [leNat_split (m := 128) (n := 128), hlow, hhigh]
  show _ = (Expression.eval env inp.digestLo).val
      + 2 ^ 128 * (Expression.eval env inp.digestHi).val
  rfl

/-- The canonical representative of `n - x` for `x.val < n`. -/
theorem val_nFp_sub (x : Fp) (hx : x.val < Challenge.Specs.ECDSAP256.n) :
    ((Challenge.Specs.ECDSAP256.n : Fp) - x).val
      = Challenge.Specs.ECDSAP256.n - x.val := by
  have : NeZero p := ⟨by decide⟩
  have hn : Challenge.Specs.ECDSAP256.n < p := n_lt_p
  rw [ZMod.val_sub (a := (Challenge.Specs.ECDSAP256.n : Fp)) (b := x) (by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn]
    exact Nat.le_of_lt hx)]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn]

/-- The 256 `r` bits recompose to the canonical representative of `r`. -/
theorem leNat_rb_eq (env : Environment Fp) (inp : Var Input Fp) (b : Bits)
    (h : Expression.eval env (linComb b.rb 0 256) = Expression.eval env inp.r)
    (hb : ∀ k : Fin 256, Expression.eval env (b.rb.get k) = 0 ∨
      Expression.eval env (b.rb.get k) = 1)
    (hbound : leNat (fun i : Fin 256 => (Expression.eval env (b.rb.get i)).val) < p) :
    leNat (fun i : Fin 256 => (Expression.eval env (b.rb.get i)).val)
      = (Expression.eval env inp.r).val := by
  have hget : ∀ (i : Nat) (hi : i < 256), b.rb.getD i (cst 0) = b.rb.get ⟨i, hi⟩ :=
    fun i hi => getD_eq_get hi
  have hv : ∀ i : Fin 256, Expression.eval env (b.rb.getD (0 + i.val) (cst 0)) = 0 ∨
      Expression.eval env (b.rb.getD (0 + i.val) (cst 0)) = 1 := by
    intro i
    rw [Nat.zero_add, hget i.val (by omega)]
    exact hb _
  have h1 : leSum (fun i : Fin 256 => Expression.eval env (b.rb.getD (0 + i.val) (cst 0)))
      = Expression.eval env inp.r := by
    rw [← eval_linComb]; exact h
  have h2 : (leSum (fun i : Fin 256 =>
      Expression.eval env (b.rb.getD (0 + i.val) (cst 0)))).val
      = leNat (fun i : Fin 256 =>
          (Expression.eval env (b.rb.getD (0 + i.val) (cst 0))).val) :=
    val_leSum' _ hv (by
      rw [← leNat_congr (fun i => by rw [Nat.zero_add, hget i.val (by omega)])]
      exact hbound)
  have h3 : leNat (fun i : Fin 256 => (Expression.eval env (b.rb.get ⟨i.val, by omega⟩)).val)
      = leNat (fun i : Fin 256 =>
          (Expression.eval env (b.rb.getD (0 + i.val) (cst 0))).val) :=
    leNat_congr fun i => by rw [Nat.zero_add, hget i.val (by omega)]
  rw [h3, ← h2, h1]

/-- The 256 `t = n - s` bits recompose to `n - s.val`. -/
theorem leNat_sb_eq (env : Environment Fp) (inp : Var Input Fp) (b : Bits)
    (h : Expression.eval env (linComb b.sb 0 256)
      = Expression.eval env (cst (Challenge.Specs.ECDSAP256.n : Fp) - inp.s))
    (hb : ∀ k : Fin 256, Expression.eval env (b.sb.get k) = 0 ∨
      Expression.eval env (b.sb.get k) = 1)
    (hbound : leNat (fun i : Fin 256 => (Expression.eval env (b.sb.get i)).val) < p)
    (hsn : (Expression.eval env inp.s).val < Challenge.Specs.ECDSAP256.n) :
    leNat (fun i : Fin 256 => (Expression.eval env (b.sb.get i)).val)
      = Challenge.Specs.ECDSAP256.n - (Expression.eval env inp.s).val := by
  have hget : ∀ (i : Nat) (hi : i < 256), b.sb.getD i (cst 0) = b.sb.get ⟨i, hi⟩ :=
    fun i hi => getD_eq_get hi
  have hv : ∀ i : Fin 256, Expression.eval env (b.sb.getD (0 + i.val) (cst 0)) = 0 ∨
      Expression.eval env (b.sb.getD (0 + i.val) (cst 0)) = 1 := by
    intro i
    rw [Nat.zero_add, hget i.val (by omega)]
    exact hb _
  have h1 : leSum (fun i : Fin 256 => Expression.eval env (b.sb.getD (0 + i.val) (cst 0)))
      = Expression.eval env (cst (Challenge.Specs.ECDSAP256.n : Fp) - inp.s) := by
    rw [← eval_linComb]; exact h
  have h2 : (leSum (fun i : Fin 256 =>
      Expression.eval env (b.sb.getD (0 + i.val) (cst 0)))).val
      = leNat (fun i : Fin 256 =>
          (Expression.eval env (b.sb.getD (0 + i.val) (cst 0))).val) :=
    val_leSum' _ hv (by
      rw [← leNat_congr (fun i => by rw [Nat.zero_add, hget i.val (by omega)])]
      exact hbound)
  have h3 : leNat (fun i : Fin 256 => (Expression.eval env (b.sb.get ⟨i.val, by omega⟩)).val)
      = leNat (fun i : Fin 256 =>
          (Expression.eval env (b.sb.getD (0 + i.val) (cst 0))).val) :=
    leNat_congr fun i => by rw [Nat.zero_add, hget i.val (by omega)]
  rw [h3, ← h2, h1, eval_sub, eval_cst, val_nFp_sub _ hsn]

/-- `leNat` of the field values of a Boolean hint vector is `leNat` of its
`aNatOf` reading, which is what the comparator bounds. -/
theorem leNat_val_eq_aNatOf (env : Environment Fp) (v : Vector E 256)
    (hv : ∀ k : Fin 256, Expression.eval env (v.get k) = 0 ∨
      Expression.eval env (v.get k) = 1) :
    leNat (fun i : Fin 256 => (Expression.eval env (v.get i)).val)
      = leNat (fun i : Fin 256 =>
          aNatOf (fun k => Expression.eval env (v.getD k (cst 0))) i) := by
  refine leNat_congr fun i => ?_
  have hgd : Expression.eval env (v.getD i.val (cst 0)) = Expression.eval env (v.get i) := by
    rw [getD_eq_get i.isLt]
  rcases hv i with h | h
  · rw [h, ZMod.val_zero]
    simp only [aNatOf, hgd, h]
    rfl
  · rw [h, ZMod.val_one p]
    simp only [aNatOf, hgd, h]
    rfl



/-! ## Canonical representatives and the affine/projective bridge -/

/-- The canonical representative of `n - x` for `x.val ≤ n`. -/
theorem val_nFp_sub_le (x : Fp) (hx : x.val ≤ Challenge.Specs.ECDSAP256.n) :
    ((Challenge.Specs.ECDSAP256.n : Fp) - x).val
      = Challenge.Specs.ECDSAP256.n - x.val := by
  have : NeZero p := ⟨by decide⟩
  have hn : Challenge.Specs.ECDSAP256.n < p := n_lt_p
  rw [ZMod.val_sub (a := (Challenge.Specs.ECDSAP256.n : Fp)) (b := x) (by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn]; exact hx)]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn]

/-- Nonsingularity of an affine point implies the Mathlib `IsOnCurve` predicate
(which is only the curve equation). -/
theorem ns_isOnCurve (x y : Fp) (h : NS x y) :
    (⟨x, y⟩ : AffinePoint K).IsOnCurve params := by
  unfold NS AffinePoint.IsOnCurve at *
  obtain ⟨h1, -⟩ := h
  rw [WeierstrassCurve.Affine.equation_iff'] at h1
  simp only [CurveParameters.toMathlib] at h1 ⊢
  linear_combination h1

/-- `toAffineLift` of the Mathlib point attached to an affine point is that
affine point. -/
theorem toAffineLift_Qpt (Q : AffinePoint K) (hQ : Q.IsOnCurve params) (hns : NS Q.X Q.Y) :
    WeierstrassCurve.Projective.Point.toAffineLift (Qpt Q hQ)
      = WeierstrassCurve.Affine.Point.some Q.X Q.Y hns := by
  simp only [Qpt, ProjectivePoint.toMathlibPoint]
  rw [WeierstrassCurve.Projective.Point.toAffineLift_eq]
  show WeierstrassCurve.Projective.Point.toAffine (params.toMathlib.toProjective) ![Q.X, Q.Y, 1]
    = WeierstrassCurve.Affine.Point.some Q.X Q.Y hns
  have hns' : WeierstrassCurve.Projective.Nonsingular (params.toMathlib.toProjective) ![Q.X, Q.Y, 1] :=
    isOnCurve_implies_nonsingular Q.toProjective params (toProjective_on_curve hQ)
  rw [WeierstrassCurve.Projective.Point.toAffine_some (W := params.toMathlib.toProjective) hns']


theorem soundness_ops_of_snd {env : Environment Fp} {α : Type} {c : C α} {n : Nat}
    (h : ConstraintsHold.Soundness env (c n).2) :
    ConstraintsHold.Soundness env (c.operations n) := h

theorem toAffineLift_nsmul (k : Nat) (P : Grp) :
    WeierstrassCurve.Projective.Point.toAffineLift (k • P)
      = k • WeierstrassCurve.Projective.Point.toAffineLift P :=
  map_nsmul (WeierstrassCurve.Projective.Point.toAffineAddEquiv
    (W := params.toMathlib.toProjective)) k P

theorem toAffineLift_toMathlibPoint (R : AffinePoint K) (hR : R.IsOnCurve params)
    (hns : NS R.X R.Y) :
    WeierstrassCurve.Projective.Point.toAffineLift
        (R.toProjective.toMathlibPoint params (toProjective_on_curve hR))
      = WeierstrassCurve.Affine.Point.some R.X R.Y hns :=
  toAffineLift_Qpt R hR hns

theorem main_group_algebra
    (Hpt QptA RptA : WeierstrassCurve.Affine.Point Wp) (E r t : Nat)
    (ep target : WeierstrassCurve.Affine.Point Wp)
    (hep : ep = Hpt + WeierstrassCurve.Projective.Point.toAffineLift (E • Gpt))
    (htarget : target = (r : ℤ) • QptA + (t : ℤ) • RptA - Hpt)
    (hneg : target = -ep)
    (Q : AffinePoint K) (hQ : Q.IsOnCurve params) (hQns : NS Q.X Q.Y)
    (R : AffinePoint K) (hR : R.IsOnCurve params) (hRns : NS R.X R.Y)
    (hQptA : QptA = WeierstrassCurve.Affine.Point.some Q.X Q.Y hQns)
    (hRptA : RptA = WeierstrassCurve.Affine.Point.some R.X R.Y hRns) :
    E • Gpt + r • Qpt Q hQ
      + t • R.toProjective.toMathlibPoint params (toProjective_on_curve hR) = 0 := by
  have hinj := (WeierstrassCurve.Projective.Point.toAffineAddEquiv
    (W := params.toMathlib.toProjective)).injective
  apply hinj
  change WeierstrassCurve.Projective.Point.toAffineLift
      (E • Gpt + r • Qpt Q hQ
        + t • R.toProjective.toMathlibPoint params (toProjective_on_curve hR))
    = WeierstrassCurve.Projective.Point.toAffineLift 0
  rw [toAffineLift_add, toAffineLift_add, toAffineLift_nsmul, toAffineLift_nsmul,
    toAffineLift_nsmul, toAffineLift_zero,
    toAffineLift_Qpt Q hQ hQns, toAffineLift_toMathlibPoint R hR hRns]
  rw [hQptA, hRptA] at htarget
  rw [hneg, hep] at htarget
  rw [toAffineLift_nsmul] at htarget
  have h3 : r • WeierstrassCurve.Affine.Point.some Q.X Q.Y hQns
      + t • WeierstrassCurve.Affine.Point.some R.X R.Y hRns
      = - (E • WeierstrassCurve.Projective.Point.toAffineLift Gpt) := by
    have h4 : (r : ℤ) • WeierstrassCurve.Affine.Point.some Q.X Q.Y hQns
        + (t : ℤ) • WeierstrassCurve.Affine.Point.some R.X R.Y hRns
        = - (E • WeierstrassCurve.Projective.Point.toAffineLift Gpt) := by
      have h6 : -(Hpt + E • WeierstrassCurve.Projective.Point.toAffineLift Gpt) + Hpt
          = - (E • WeierstrassCurve.Projective.Point.toAffineLift Gpt) := by abel
      rw [← h6, htarget]
      abel
    rw [show (r : ℤ) • WeierstrassCurve.Affine.Point.some Q.X Q.Y hQns
          = r • WeierstrassCurve.Affine.Point.some Q.X Q.Y hQns from
        Nat.cast_smul_eq_nsmul (M := WeierstrassCurve.Affine.Point Wp) (R := ℤ) r _,
      show (t : ℤ) • WeierstrassCurve.Affine.Point.some R.X R.Y hRns
          = t • WeierstrassCurve.Affine.Point.some R.X R.Y hRns from
        Nat.cast_smul_eq_nsmul (M := WeierstrassCurve.Affine.Point Wp) (R := ℤ) t _] at h4
    exact h4
  rw [add_assoc, h3]
  abel


theorem shiftedTables_out (h q r : Pt) (n : Nat) (hdeg : deg h.1 = 1) :
    (shiftedTables h q r).output n
      = { p0 := (var ⟨n + 6⟩, var ⟨n + 7⟩)
          p1 := (var ⟨n + 10⟩, var ⟨n + 11⟩)
          p2 := (var ⟨n + 14⟩, var ⟨n + 15⟩)
          p3 := (var ⟨n + 18⟩, var ⟨n + 19⟩)
          m0 := (var ⟨n + 6⟩, -var ⟨n + 7⟩)
          m1 := (var ⟨n + 22⟩, var ⟨n + 23⟩)
          m2 := (var ⟨n + 26⟩, var ⟨n + 27⟩)
          m3 := (var ⟨n + 30⟩, var ⟨n + 31⟩) } := by
  simp only [shiftedTables, circuit_norm, affAdd_localLength', affDouble_localLength' hdeg,
    affAdd_output, affDouble_output, negPt]

theorem tables_x0_fst (h q r : Pt) (n : Nat) (hdeg : deg h.1 = 1) (j : Nat) :
    (((shiftedTables h q r).output n).x0 j).1 = var ⟨n + 6⟩ := by
  rw [shiftedTables_out h q r n hdeg]; simp only [Tables.x0]; split <;> rfl

theorem tables_x0_snd (h q r : Pt) (n : Nat) (hdeg : deg h.1 = 1) (j : Nat) :
    (((shiftedTables h q r).output n).x0 j).2
      = if j % 2 == 0 then var ⟨n + 7⟩ else -var ⟨n + 7⟩ := by
  rw [shiftedTables_out h q r n hdeg]; simp only [Tables.x0]; split <;> rfl

theorem tables_x1_fst (h q r : Pt) (n : Nat) (hdeg : deg h.1 = 1) (j : Nat) :
    (((shiftedTables h q r).output n).x1 j).1
      = if j % 2 == 0 then var ⟨n + 10⟩ else var ⟨n + 22⟩ := by
  rw [shiftedTables_out h q r n hdeg]; simp only [Tables.x1]; split <;> rfl

theorem tables_x1_snd (h q r : Pt) (n : Nat) (hdeg : deg h.1 = 1) (j : Nat) :
    (((shiftedTables h q r).output n).x1 j).2
      = if j % 2 == 0 then var ⟨n + 11⟩ else var ⟨n + 23⟩ := by
  rw [shiftedTables_out h q r n hdeg]; simp only [Tables.x1]; split <;> rfl

theorem tables_x2_fst (h q r : Pt) (n : Nat) (hdeg : deg h.1 = 1) (j : Nat) :
    (((shiftedTables h q r).output n).x2 j).1
      = if j % 2 == 0 then var ⟨n + 14⟩ else var ⟨n + 26⟩ := by
  rw [shiftedTables_out h q r n hdeg]; simp only [Tables.x2]; split <;> rfl

theorem tables_x2_snd (h q r : Pt) (n : Nat) (hdeg : deg h.1 = 1) (j : Nat) :
    (((shiftedTables h q r).output n).x2 j).2
      = if j % 2 == 0 then var ⟨n + 15⟩ else var ⟨n + 27⟩ := by
  rw [shiftedTables_out h q r n hdeg]; simp only [Tables.x2]; split <;> rfl

theorem tables_x3_fst (h q r : Pt) (n : Nat) (hdeg : deg h.1 = 1) (j : Nat) :
    (((shiftedTables h q r).output n).x3 j).1
      = if j % 2 == 0 then var ⟨n + 18⟩ else var ⟨n + 30⟩ := by
  rw [shiftedTables_out h q r n hdeg]; simp only [Tables.x3]; split <;> rfl

theorem tables_x3_snd (h q r : Pt) (n : Nat) (hdeg : deg h.1 = 1) (j : Nat) :
    (((shiftedTables h q r).output n).x3 j).2
      = if j % 2 == 0 then var ⟨n + 19⟩ else var ⟨n + 31⟩ := by
  rw [shiftedTables_out h q r n hdeg]; simp only [Tables.x3]; split <;> rfl

theorem sigma_eq (j : Nat) : sigma j = if j % 2 == 0 then (1 : ℤ) else -1 := by
  unfold sigma
  by_cases hj : j % 2 == 0
  · rw [if_pos hj]
    exact Even.neg_one_pow (Nat.even_iff.mpr (by simpa using hj))
  · rw [if_neg hj]
    have h1 : j % 2 = 1 := by
      have h2 : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have h3 : j % 2 ≠ 0 := by simpa using hj
      omega
    exact Odd.neg_one_pow (Nat.odd_iff.mpr h1)

theorem shiftedTables_htab (env : Environment Fp) (h q r : Pt) (n : Nat) (hdeg : deg h.1 = 1)
    (hH : NS (Expression.eval env h.1) (Expression.eval env h.2))
    (hQ : NS (Expression.eval env q.1) (Expression.eval env q.2))
    (hR : NS (Expression.eval env r.1) (Expression.eval env r.2))
    (hy : 2 * Expression.eval env h.2 ≠ 0)
    (hdx1 : Expression.eval env h.1 - env.get (n + 2) ≠ 0)
    (hdx2 : Expression.eval env q.1 - env.get (n + 6) ≠ 0)
    (hdx3 : Expression.eval env r.1 - env.get (n + 6) ≠ 0)
    (hdx4 : Expression.eval env r.1 - env.get (n + 10) ≠ 0)
    (hdx5 : Expression.eval env r.1 - env.get (n + 22) ≠ 0)
    (hc : ConstraintsHold.Soundness env ((shiftedTables h q r).operations n)) :
    ∀ (j : Nat) (hj : j < 256) (v w : Fp), (v = 0 ∨ v = 1) → (w = 0 ∨ w = 1) →
      ∃ hns : NS (if v = 0 then
            (if w = 0 then Expression.eval env (((shiftedTables h q r).output n).x0 j).1
              else Expression.eval env (((shiftedTables h q r).output n).x2 j).1)
          else (if w = 0 then Expression.eval env (((shiftedTables h q r).output n).x1 j).1
            else Expression.eval env (((shiftedTables h q r).output n).x3 j).1))
          (if v = 0 then
            (if w = 0 then Expression.eval env (((shiftedTables h q r).output n).x0 j).2
              else Expression.eval env (((shiftedTables h q r).output n).x2 j).2)
          else (if w = 0 then Expression.eval env (((shiftedTables h q r).output n).x1 j).2
            else Expression.eval env (((shiftedTables h q r).output n).x3 j).2)),
        WeierstrassCurve.Affine.Point.some
          (if v = 0 then
            (if w = 0 then Expression.eval env (((shiftedTables h q r).output n).x0 j).1
              else Expression.eval env (((shiftedTables h q r).output n).x2 j).1)
          else (if w = 0 then Expression.eval env (((shiftedTables h q r).output n).x1 j).1
            else Expression.eval env (((shiftedTables h q r).output n).x3 j).1))
          (if v = 0 then
            (if w = 0 then Expression.eval env (((shiftedTables h q r).output n).x0 j).2
              else Expression.eval env (((shiftedTables h q r).output n).x2 j).2)
          else (if w = 0 then Expression.eval env (((shiftedTables h q r).output n).x1 j).2
            else Expression.eval env (((shiftedTables h q r).output n).x3 j).2)) hns
          = (3 * sigma j) • WeierstrassCurve.Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH
            + (if v = 1 then (1 : ℤ) else 0) • WeierstrassCurve.Affine.Point.some (Expression.eval env q.1) (Expression.eval env q.2) hQ
            + (if w = 1 then (1 : ℤ) else 0) • WeierstrassCurve.Affine.Point.some (Expression.eval env r.1) (Expression.eval env r.2) hR := by
  intro j hj v w hv hw
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, e0, e1, e2, e3, e4, e5, e6, e7⟩ :=
    shiftedTables_spec env h q r n hdeg hH hQ hR hy hdx1 hdx2 hdx3 hdx4 hdx5 hc
  rw [tables_x0_fst h q r n hdeg j, tables_x0_snd h q r n hdeg j,
    tables_x1_fst h q r n hdeg j, tables_x1_snd h q r n hdeg j,
    tables_x2_fst h q r n hdeg j, tables_x2_snd h q r n hdeg j,
    tables_x3_fst h q r n hdeg j, tables_x3_snd h q r n hdeg j]
  simp only [eval_var, eval_neg]
  set Hpt := WeierstrassCurve.Affine.Point.some (Expression.eval env h.1) (Expression.eval env h.2) hH
    with hHpt
  set Qpt := WeierstrassCurve.Affine.Point.some (Expression.eval env q.1) (Expression.eval env q.2) hQ
    with hQpt
  set Rpt := WeierstrassCurve.Affine.Point.some (Expression.eval env r.1) (Expression.eval env r.2) hR
    with hRpt
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
  · simp only [ite_true, if_neg (one_ne_zero : (1 : Fp) ≠ 0),
      if_neg (zero_ne_one : (0 : Fp) ≠ 1), eval_var, eval_neg]
    by_cases hj2 : j % 2 == 0
    · simp only [if_pos hj2, eval_var, eval_neg]
      have hz : (3 * sigma j) • Hpt = 3 • Hpt := by
        rw [sigma_eq j, if_pos hj2, mul_one]
        exact Nat.cast_smul_eq_nsmul (M := WeierstrassCurve.Affine.Point Wp) (R := ℤ) 3 Hpt
      refine ⟨h0, ?_⟩
      rw [e0, hz]
      simp [zero_zsmul, add_zero]
    · simp only [if_neg hj2, eval_var, eval_neg]
      have hz : (3 * sigma j) • Hpt = -(3 • Hpt) := by
        rw [sigma_eq j, if_neg hj2]
        have h3 : ((3 : ℤ)) • Hpt = 3 • Hpt :=
          Nat.cast_smul_eq_nsmul (M := WeierstrassCurve.Affine.Point Wp) (R := ℤ) 3 Hpt
        rw [show (3 : ℤ) * (-1) = -(3 : ℤ) from by norm_num, neg_zsmul, h3]
      refine ⟨h4, ?_⟩
      rw [e4, hz]
      simp [zero_zsmul, add_zero]
  · simp only [ite_true, if_neg (one_ne_zero : (1 : Fp) ≠ 0),
      if_neg (zero_ne_one : (0 : Fp) ≠ 1), eval_var, eval_neg]
    by_cases hj2 : j % 2 == 0
    · simp only [if_pos hj2, eval_var, eval_neg]
      have hz : (3 * sigma j) • Hpt = 3 • Hpt := by
        rw [sigma_eq j, if_pos hj2, mul_one]
        exact Nat.cast_smul_eq_nsmul (M := WeierstrassCurve.Affine.Point Wp) (R := ℤ) 3 Hpt
      refine ⟨h2, ?_⟩
      rw [e2, hz]
      simp [zero_zsmul, one_zsmul, add_zero]
    · simp only [if_neg hj2, eval_var, eval_neg]
      have hz : (3 * sigma j) • Hpt = -(3 • Hpt) := by
        rw [sigma_eq j, if_neg hj2]
        have h3 : ((3 : ℤ)) • Hpt = 3 • Hpt :=
          Nat.cast_smul_eq_nsmul (M := WeierstrassCurve.Affine.Point Wp) (R := ℤ) 3 Hpt
        rw [show (3 : ℤ) * (-1) = -(3 : ℤ) from by norm_num, neg_zsmul, h3]
      refine ⟨h6, ?_⟩
      rw [e6, hz]
      simp [zero_zsmul, one_zsmul, add_zero]
  · simp only [ite_true, if_neg (one_ne_zero : (1 : Fp) ≠ 0),
      if_neg (zero_ne_one : (0 : Fp) ≠ 1), eval_var, eval_neg]
    by_cases hj2 : j % 2 == 0
    · simp only [if_pos hj2, eval_var, eval_neg]
      have hz : (3 * sigma j) • Hpt = 3 • Hpt := by
        rw [sigma_eq j, if_pos hj2, mul_one]
        exact Nat.cast_smul_eq_nsmul (M := WeierstrassCurve.Affine.Point Wp) (R := ℤ) 3 Hpt
      refine ⟨h1, ?_⟩
      rw [e1, hz]
      simp [zero_zsmul, one_zsmul, add_zero]
    · simp only [if_neg hj2, eval_var, eval_neg]
      have hz : (3 * sigma j) • Hpt = -(3 • Hpt) := by
        rw [sigma_eq j, if_neg hj2]
        have h3 : ((3 : ℤ)) • Hpt = 3 • Hpt :=
          Nat.cast_smul_eq_nsmul (M := WeierstrassCurve.Affine.Point Wp) (R := ℤ) 3 Hpt
        rw [show (3 : ℤ) * (-1) = -(3 : ℤ) from by norm_num, neg_zsmul, h3]
      refine ⟨h5, ?_⟩
      rw [e5, hz]
      simp [zero_zsmul, one_zsmul, add_zero]
  · simp only [ite_true, if_neg (one_ne_zero : (1 : Fp) ≠ 0),
      if_neg (zero_ne_one : (0 : Fp) ≠ 1), eval_var, eval_neg]
    by_cases hj2 : j % 2 == 0
    · simp only [if_pos hj2, eval_var, eval_neg]
      have hz : (3 * sigma j) • Hpt = 3 • Hpt := by
        rw [sigma_eq j, if_pos hj2, mul_one]
        exact Nat.cast_smul_eq_nsmul (M := WeierstrassCurve.Affine.Point Wp) (R := ℤ) 3 Hpt
      refine ⟨h3, ?_⟩
      rw [e3, hz]
      simp [zero_zsmul, one_zsmul, add_zero]
    · simp only [if_neg hj2, eval_var, eval_neg]
      have hz : (3 * sigma j) • Hpt = -(3 • Hpt) := by
        rw [sigma_eq j, if_neg hj2]
        have h3 : ((3 : ℤ)) • Hpt = 3 • Hpt :=
          Nat.cast_smul_eq_nsmul (M := WeierstrassCurve.Affine.Point Wp) (R := ℤ) 3 Hpt
        rw [show (3 : ℤ) * (-1) = -(3 : ℤ) from by norm_num, neg_zsmul, h3]
      refine ⟨h7, ?_⟩
      rw [e7, hz]
      simp [zero_zsmul, one_zsmul, add_zero]


theorem prefVal_rev_nat (f : Nat → Nat) :
    prefVal (fun j => f (255 - j)) 256 = leNat (fun i : Fin 256 => f i.val) := by
  have h1 : prefVal (fun j => f (255 - j)) 256
      = prefVal (fun j => (fun i : Fin 256 => f i.val) ⟨255 - j, by omega⟩) 256 := rfl
  rw [h1, prefVal_rev (fun i : Fin 256 => f i.val)]

theorem seed_hx_deg (inp : Var Input Fp) (n : Nat) : deg (seedPhase inp n).1.hx = 1 := by
  show deg ((seedPhase inp).output n).hx = 1
  rw [seedPhase_out]
  simp only [hint, witnessField, Circuit.output, deg, Challenge.CostR1CS.degree]

theorem affDouble_hy (env : Environment Fp) (p : Pt) (n : Nat) (hdeg : deg p.1 = 1)
    (hA : NS (Expression.eval env p.1) (Expression.eval env p.2))
    (h : ConstraintsHold.Soundness env ((affDouble p).operations n)) :
    2 * Expression.eval env p.2 ≠ 0 := by
  have hml : matLen (.mul p.1 p.1) = 1 := matLen_mul_of_deg_one hdeg hdeg
  simp only [affDouble, mm, circuit_norm, pm] at h
  obtain ⟨r1, r2, -, -⟩ := h
  have hlen : Operations.localLength (mat (.mul p.1 p.1) n).2 = matLen (.mul p.1 p.1) :=
    mat_localLength_eq _ n
  rw [hlen, hml] at r2
  have hxx : Expression.eval env ((mat (.mul p.1 p.1) n).1)
      = Expression.eval env p.1 * Expression.eval env p.1 := by
    rw [mat_output_eq]
    rw [mat_eval_gen (.mul p.1 p.1) n env
      { assert := fun e => Expression.eval env e = 0
        lookup := fun l => l.Soundness env
        interact := fun i => i.Guarantees env
        subcircuit := fun {m} s => s.Assumptions env → s.Spec env }
      (fun x hx => hx) r1]
    simp only [Expression.eval]
  have h2 : (2 * Expression.eval env p.2) * env.get (n + 1)
      = 3 * (Expression.eval env p.1 * Expression.eval env p.1) + pa := by
    have h2' : Expression.eval env (sc 2 p.2) * env.get (n + 1)
        - Expression.eval env (sc 3 (mat (.mul p.1 p.1) n).1)
        = Expression.eval env (cst pa) := sub_eq_zero.mp r2
    rw [StandardECDSA.eval_sc, StandardECDSA.eval_sc, StandardECDSA.eval_cst, hxx] at h2'
    rw [eq_add_of_sub_eq h2']
    exact add_comm _ _
  have hCurve : (Expression.eval env p.2)^2
      = (Expression.eval env p.1)^3 + params.a * Expression.eval env p.1 + params.b := by
    unfold NS at hA
    obtain ⟨h1, -⟩ := hA
    rw [WeierstrassCurve.Affine.equation_iff'] at h1
    simp only [CurveParameters.toMathlib] at h1
    linear_combination h1
  refine StandardECDSA.Math.ElmAlgebra.double_denominator_ne params.a params.b
    (Expression.eval env p.1) (Expression.eval env p.2) (env.get (n + 1)) (by decide)
    discriminant_ne_zero hCurve ?_
  rw [h2]
  have hpa : pa = params.a := rfl
  rw [hpa]
  ring

theorem shiftedTables_hy (env : Environment Fp) (h q r : Pt) (n : Nat) (hdeg : deg h.1 = 1)
    (hH : NS (Expression.eval env h.1) (Expression.eval env h.2))
    (hc : ConstraintsHold.Soundness env ((shiftedTables h q r).operations n)) :
    2 * Expression.eval env h.2 ≠ 0 := by
  simp only [shiftedTables, circuit_norm] at hc
  simp only [affAdd_localLength', affDouble_localLength' hdeg] at hc
  obtain ⟨a1, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hc
  exact affDouble_hy env h n hdeg hH a1

set_option linter.constructorNameAsVariable false in
/-- `eval` of `inp.r + sc nFp o`. -/
theorem eval_r_plus_overflow (env : Environment Fp) (inp : Var Input Fp) (o : E) :
    Expression.eval env (inp.r + sc nFp o)
      = Expression.eval env inp.r + (StandardECDSA.n : Fp) * Expression.eval env o := by
  simp only [eval_add', eval_sc', eval_cst, nFp]

theorem main_soundness (inp : Var Input Fp) (env : Environment Fp) (n : Nat)
    (hc : ConstraintsHold.Soundness env ((main inp).operations n)) :
    standardVerify (Expression.eval env inp.pkX) (Expression.eval env inp.pkY)
      (Expression.eval env inp.digestLo) (Expression.eval env inp.digestHi)
      (Expression.eval env inp.r) (Expression.eval env inp.s) := by
  rw [standard_iff_signaturePoint]
  simp only [signaturePointVerify]
  rw [main_ops] at hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := soundness_append9 hc
  set n1 := n + Operations.localLength (seedPhase inp n).2 with hn1
  set n2 := n1 + Operations.localLength (curvePhase inp (seedPhase inp n).1 n1).2 with hn2
  set n3 := n2 + Operations.localLength (nonzeroPhase inp n2).2 with hn3
  set n4 := n3 + Operations.localLength (bitsPhase n3).2 with hn4
  set n5 := n4 + Operations.localLength (bindPhase inp (bitsPhase n3).1 n4).2 with hn5
  set n6 := n5 + Operations.localLength
    (cmpPhase (bitsPhase n3).1 (seedPhase inp n).1.overflow n5).2 with hn6
  set n7 := n6 + Operations.localLength
    (fixedBase ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy) (bitsPhase n3).1.eb n6).2 with hn7
  set n8 := n7 + Operations.localLength
    (shiftedTables ((seedPhase inp n).1.hx, (seedPhase inp n).1.hy) (inp.pkX, inp.pkY)
      (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry) n7).2 with hn8
  -- stage facts
  have hov := seedPhase_sound inp env n h1
  obtain ⟨hQns, hRns, hHns⟩ := curvePhase_sound inp (seedPhase inp n).1 env n1 h2
  obtain ⟨hrne, htne⟩ := nonzeroPhase_sound inp env n2 h3
  obtain ⟨heb, hrb, hsb⟩ := bitsPhase_sound env n3 h4
  obtain ⟨hlo, hhi, hrbind, hsbind⟩ := bindPhase_sound inp (bitsPhase n3).1 env n4 h5
  obtain ⟨hcmpR, hcmpS, hcmpG⟩ :=
    cmpPhase_sound (bitsPhase n3).1 (seedPhase inp n).1.overflow env n5 hrb hsb h6
  -- comparator bounds in `leNat` form
  have hrb_le : leNat (fun i : Fin 256 => (Expression.eval env ((bitsPhase n3).1.rb.get i)).val)
      ≤ StandardECDSA.n - 1 := by
    rw [prefVal_rev_nat (fun k => aNatOf
      (fun k' => Expression.eval env ((bitsPhase n3).1.rb.getD k' (cst 0))) k)] at hcmpR
    rw [← leNat_val_eq_aNatOf env _ hrb] at hcmpR
    exact hcmpR
  have hsb_le : leNat (fun i : Fin 256 => (Expression.eval env ((bitsPhase n3).1.sb.get i)).val)
      ≤ StandardECDSA.n - 1 := by
    rw [prefVal_rev_nat (fun k => aNatOf
      (fun k' => Expression.eval env ((bitsPhase n3).1.sb.getD k' (cst 0))) k)] at hcmpS
    rw [← leNat_val_eq_aNatOf env _ hsb] at hcmpS
    exact hcmpS
  have hbound_rb : leNat (fun i : Fin 256 => (Expression.eval env ((bitsPhase n3).1.rb.get i)).val) < p := by
    have h := hrb_le
    have h2' := n_lt_p
    omega
  have hbound_sb : leNat (fun i : Fin 256 => (Expression.eval env ((bitsPhase n3).1.sb.get i)).val) < p := by
    have h := hsb_le
    have h2' := n_lt_p
    omega
  -- `r` bounds
  have hrv : leNat (fun i : Fin 256 => (Expression.eval env ((bitsPhase n3).1.rb.get i)).val)
      = (Expression.eval env inp.r).val :=
    leNat_rb_eq env inp (bitsPhase n3).1 hrbind hrb hbound_rb
  have hkSub : nSubOne < StandardECDSA.n := by decide
  have hrv_lt : (Expression.eval env inp.r).val < StandardECDSA.n := by
    rw [← hrv]
    have h := hrb_le
    omega
  have hrv_pos : 0 < (Expression.eval env inp.r).val := by
    have hne : (Expression.eval env inp.r).val ≠ 0 := (ZMod.val_ne_zero _).mpr hrne
    exact Nat.pos_of_ne_zero hne
  -- `s` bounds
  have hsv : ((StandardECDSA.n : Fp) - Expression.eval env inp.s).val
      = leNat (fun i : Fin 256 => (Expression.eval env ((bitsPhase n3).1.sb.get i)).val) := by
    have hget : ∀ (i : Nat) (hi : i < 256),
        (bitsPhase n3).1.sb.getD i (cst 0) = (bitsPhase n3).1.sb.get ⟨i, hi⟩ :=
      fun i hi => getD_eq_get hi
    have hv : ∀ i : Fin 256,
        Expression.eval env ((bitsPhase n3).1.sb.getD (0 + i.val) (cst 0)) = 0 ∨
        Expression.eval env ((bitsPhase n3).1.sb.getD (0 + i.val) (cst 0)) = 1 := by
      intro i; rw [Nat.zero_add, hget i.val (by omega)]; exact hsb _
    have h1' : leSum (fun i : Fin 256 =>
        Expression.eval env ((bitsPhase n3).1.sb.getD (0 + i.val) (cst 0)))
        = Expression.eval env (cst (StandardECDSA.n : Fp) - inp.s) := by
      rw [← eval_linComb]; exact hsbind
    have h2' : (leSum (fun i : Fin 256 =>
        Expression.eval env ((bitsPhase n3).1.sb.getD (0 + i.val) (cst 0)))).val
        = leNat (fun i : Fin 256 =>
            (Expression.eval env ((bitsPhase n3).1.sb.getD (0 + i.val) (cst 0))).val) :=
      val_leSum' _ hv (by
        rw [← leNat_congr (fun i => by rw [Nat.zero_add, hget i.val (by omega)])]
        exact hbound_sb)
    have h3' : leNat (fun i : Fin 256 =>
        (Expression.eval env ((bitsPhase n3).1.sb.getD (0 + i.val) (cst 0))).val)
        = leNat (fun i : Fin 256 => (Expression.eval env ((bitsPhase n3).1.sb.get i)).val) :=
      leNat_congr fun i => by rw [Nat.zero_add, hget i.val (by omega)]
    rw [← h3', ← h2', h1', eval_sub, eval_cst]
  have hsv_le : ((StandardECDSA.n : Fp) - Expression.eval env inp.s).val
      ≤ StandardECDSA.n - 1 := by
    rw [hsv]; exact hsb_le
  have hsv_ne : ((StandardECDSA.n : Fp) - Expression.eval env inp.s) ≠ 0 := by
    have h := htne
    rwa [eval_sub, eval_cst] at h
  have hsval : (Expression.eval env inp.s).val
      = StandardECDSA.n
        - ((StandardECDSA.n : Fp) - Expression.eval env inp.s).val := by
    have h1' : Expression.eval env inp.s
        = (StandardECDSA.n : Fp)
          - ((StandardECDSA.n : Fp) - Expression.eval env inp.s) := by ring
    nth_rewrite 1 [h1']
    exact val_nFp_sub_le _ (by
      have h1 := hsv_le
      have h2 : StandardECDSA.n - 1 ≤ Challenge.Specs.ECDSAP256.n := by decide
      omega)
  have hsv_ne' : ((StandardECDSA.n : Fp) - Expression.eval env inp.s).val ≠ 0 :=
    (ZMod.val_ne_zero _).mpr hsv_ne
  have hsv_lt : (Expression.eval env inp.s).val < StandardECDSA.n := by
    rw [hsval]; omega
  have hsv_pos : 0 < (Expression.eval env inp.s).val := by
    rw [hsval]; omega
  have htv : leNat (fun i : Fin 256 => (Expression.eval env ((bitsPhase n3).1.sb.get i)).val)
      = StandardECDSA.n - (Expression.eval env inp.s).val :=
    leNat_sb_eq env inp (bitsPhase n3).1 hsbind hsb hbound_sb hsv_lt
  -- digest
  have hE : digestNat env (bitsPhase n3).1.eb
      = (Digest.mk (Expression.eval env inp.digestLo)
          (Expression.eval env inp.digestHi)).toNat :=
    leNat_eb_eq_digest env inp (bitsPhase n3).1 hlo hhi heb
  -- the two phase points
  set hxE : E := (seedPhase inp n).1.hx with hhxE
  set hyE : E := (seedPhase inp n).1.hy with hhyE
  have hdegH : deg hxE = 1 := seed_hx_deg inp n
  -- fixed base
  obtain ⟨hdx0, hdx⟩ := fixedBase_dx env (hxE, hyE) (bitsPhase n3).1.eb n6 h7
  obtain ⟨hnsEp, hEp⟩ := fixedBase_spec env (hxE, hyE) (bitsPhase n3).1.eb n6 hHns heb hdx0 hdx h7
  have hEpP : WeierstrassCurve.Affine.Point.some (Expression.eval env ((fixedBase (hxE, hyE) (bitsPhase n3).1.eb).output n6).1)
        (Expression.eval env ((fixedBase (hxE, hyE) (bitsPhase n3).1.eb).output n6).2) hnsEp
      = WeierstrassCurve.Affine.Point.some (Expression.eval env hxE) (Expression.eval env hyE) hHns
        + WeierstrassCurve.Projective.Point.toAffineLift
            (digestNat env (bitsPhase n3).1.eb • Gpt) := hEp
  -- shifted tables
  have h8' : ConstraintsHold.Soundness env ((shiftedTables (hxE, hyE) (inp.pkX, inp.pkY) (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry)).operations n7) :=
    Eq.mp (congrArg (fun L => ConstraintsHold.Soundness env L)
      (shiftedTables_snd (hxE, hyE) (inp.pkX, inp.pkY) (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry) n7)) h8
  have hy := shiftedTables_hy env (hxE, hyE)
    (inp.pkX, inp.pkY) (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry)
    n7 hdegH hHns h8'
  obtain ⟨hdx1, hdx2, hdx3, hdx4, hdx5⟩ := shiftedTables_dx env
    (hxE, hyE) (inp.pkX, inp.pkY)
    (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry) n7 hdegH h8'
  have htab := shiftedTables_htab env (hxE, hyE)
    (inp.pkX, inp.pkY) (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry)
    n7 hdegH hHns hQns hRns hy hdx1 hdx2 hdx3 hdx4 hdx5 h8'
  -- the ladder
  have hacc0 : ∃ hns : NS (Expression.eval env (hxE, -hyE).1)
      (Expression.eval env (hxE, -hyE).2),
      WeierstrassCurve.Affine.Point.some (Expression.eval env (hxE, -hyE).1)
        (Expression.eval env (hxE, -hyE).2) hns
      = - WeierstrassCurve.Affine.Point.some (Expression.eval env hxE)
          (Expression.eval env hyE) hHns := by
    refine ⟨?_, ?_⟩
    · exact ns_congr (hx := rfl) (hy := eval_neg env _) (h := negPt_ns hHns)
    · refine (some_congr (hx := rfl) (hy := (eval_neg env _).symm) (h := negPt_ns hHns)
        (h' := ns_congr (hx := rfl) (hy := eval_neg env _) (h := negPt_ns hHns))).symm.trans ?_
      exact negPt_group _ _ hHns
  have hT : NS (Expression.eval env (((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.1, -((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.2).1) (Expression.eval env (((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.1, -((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.2).2) :=
    ns_congr (hx := rfl) (hy := eval_neg env (((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.2)) (h := negPt_ns hnsEp)
  have hJL : ∃ hns : NS (Expression.eval env (((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.1, -((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.2).1)
      (Expression.eval env (((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.1, -((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.2).2),
      WeierstrassCurve.Affine.Point.some (Expression.eval env (((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.1, -((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.2).1)
        (Expression.eval env (((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.1, -((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.2).2) hns
      = (leNat (fun k : Fin 256 => (Expression.eval env ((bitsPhase n3).1.rb.get k)).val) : ℤ) •
          WeierstrassCurve.Affine.Point.some (Expression.eval env inp.pkX) (Expression.eval env inp.pkY) hQns
        + (leNat (fun k : Fin 256 => (Expression.eval env ((bitsPhase n3).1.sb.get k)).val) : ℤ) •
          WeierstrassCurve.Affine.Point.some (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow))
            (Expression.eval env (seedPhase inp n).1.ry) hRns
        - WeierstrassCurve.Affine.Point.some (Expression.eval env hxE) (Expression.eval env hyE) hHns := by
    refine jointLadder_spec env (WeierstrassCurve.Affine.Point.some (Expression.eval env hxE) (Expression.eval env hyE) hHns) (WeierstrassCurve.Affine.Point.some (Expression.eval env inp.pkX) (Expression.eval env inp.pkY) hQns) (WeierstrassCurve.Affine.Point.some (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow)) (Expression.eval env (seedPhase inp n).1.ry) hRns) (hxE, -hyE) ((shiftedTables (hxE, hyE) (inp.pkX, inp.pkY) (inp.r + sc nFp (seedPhase inp n).1.overflow, (seedPhase inp n).1.ry) n7).1) (bitsPhase n3).1.rb (bitsPhase n3).1.sb (((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.1, -((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.2) n8 hacc0 hrb hsb htab hT h9
  obtain ⟨hnsT, hTgt⟩ := hJL
  have hneg : WeierstrassCurve.Affine.Point.some (Expression.eval env (((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.1, -((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.2).1)
      (Expression.eval env (((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.1, -((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.2).2) hnsT
      = - WeierstrassCurve.Affine.Point.some (Expression.eval env ((fixedBase (hxE, hyE) (bitsPhase n3).1.eb).output n6).1)
          (Expression.eval env ((fixedBase (hxE, hyE) (bitsPhase n3).1.eb).output n6).2) hnsEp := by
    exact (some_congr (hx := rfl) (hy := eval_neg env (((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.2))
      (h := hT) (h' := negPt_ns hnsEp)).trans (negPt_group _ _ hnsEp)
  -- the group algebra
  have hzero := main_group_algebra
    (WeierstrassCurve.Affine.Point.some (Expression.eval env (seedPhase inp n).1.hx)
      (Expression.eval env (seedPhase inp n).1.hy) hHns)
    (WeierstrassCurve.Affine.Point.some (Expression.eval env inp.pkX) (Expression.eval env inp.pkY) hQns)
    (WeierstrassCurve.Affine.Point.some (Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow))
      (Expression.eval env (seedPhase inp n).1.ry) hRns)
    (digestNat env (bitsPhase n3).1.eb)
    (leNat (fun k : Fin 256 => (Expression.eval env ((bitsPhase n3).1.rb.get k)).val))
    (leNat (fun k : Fin 256 => (Expression.eval env ((bitsPhase n3).1.sb.get k)).val))
    (WeierstrassCurve.Affine.Point.some (Expression.eval env ((fixedBase (hxE, hyE) (bitsPhase n3).1.eb).output n6).1)
      (Expression.eval env ((fixedBase (hxE, hyE) (bitsPhase n3).1.eb).output n6).2) hnsEp)
    (WeierstrassCurve.Affine.Point.some (Expression.eval env (((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.1, -((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.2).1)
      (Expression.eval env (((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.1, -((fixedBase (hxE, hyE) (bitsPhase n3).1.eb) n6).1.2).2) hnsT)
    hEpP hTgt hneg
    ⟨Expression.eval env inp.pkX, Expression.eval env inp.pkY⟩
    (ns_isOnCurve _ _ hQns) hQns
    ⟨Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow),
      Expression.eval env (seedPhase inp n).1.ry⟩
    (ns_isOnCurve _ _ hRns) hRns rfl rfl
  -- the overflow bound
  have hovv : (Expression.eval env (seedPhase inp n).1.overflow).val = 0 ∨
      (Expression.eval env (seedPhase inp n).1.overflow).val = 1 := by
    rcases hov with h | h
    · exact Or.inl (by rw [h, ZMod.val_zero])
    · exact Or.inr (by rw [h, ZMod.val_one])
  have hov1 : Expression.eval env (seedPhase inp n).1.overflow = 1 →
      leNat (fun i : Fin 256 => (Expression.eval env ((bitsPhase n3).1.rb.get i)).val)
        ≤ p - StandardECDSA.n - 1 := by
    intro hg
    have h2' := hcmpG hg
    rw [prefVal_rev_nat (fun k => aNatOf
      (fun k' => Expression.eval env ((bitsPhase n3).1.rb.getD k' (cst 0))) k)] at h2'
    rw [← leNat_val_eq_aNatOf env _ hrb] at h2'
    exact h2'
  have hrn : (Expression.eval env inp.r).val
      + StandardECDSA.n
        * (Expression.eval env (seedPhase inp n).1.overflow).val < p := by
    rcases hovv with h | h
    · rw [h, Nat.mul_zero, Nat.add_zero]; exact lt_trans hrv_lt n_lt_p
    · rw [h, Nat.mul_one]
      have hg : Expression.eval env (seedPhase inp n).1.overflow = 1 := by
        rw [← ZMod.natCast_zmod_val (Expression.eval env (seedPhase inp n).1.overflow), h,
          Nat.cast_one]
      have hle := hov1 hg
      rw [hrv] at hle
      have h2' := n_lt_p
      omega
  -- assemble
  refine ⟨ns_isOnCurve _ _ hQns, hrv_pos, hrv_lt, hsv_pos, hsv_lt,
    ⟨Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow),
      Expression.eval env (seedPhase inp n).1.ry⟩,
    ns_isOnCurve _ _ hRns, ?_, ?_⟩
  · refine (projectiveEquiv_iff_toMathlib
      (sigW ⟨Expression.eval env inp.pkX, Expression.eval env inp.pkY⟩
        (Expression.eval env inp.r) (Expression.eval env inp.s)
        (Digest.mk (Expression.eval env inp.digestLo) (Expression.eval env inp.digestHi)).toNat
        ⟨Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow),
          Expression.eval env (seedPhase inp n).1.ry⟩)
      infinityPoint ?_ (infinity_on_curve params)).mpr ?_
    · exact sigW_on_curve _ (ns_isOnCurve _ _ hQns) _ _ _ _ (ns_isOnCurve _ _ hRns)
    · rw [infinity_toMathlib,
        sigW_toMathlib _ (ns_isOnCurve _ _ hQns) _ _ _ _ (ns_isOnCurve _ _ hRns) hrv_lt hsv_pos]
      rw [← hE, ← hrv, ← htv]
      exact hzero
  · have hRX : (⟨Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow),
        Expression.eval env (seedPhase inp n).1.ry⟩ : AffinePoint K).X
        = (((Expression.eval env inp.r).val
          + StandardECDSA.n
            * (Expression.eval env (seedPhase inp n).1.overflow).val : Nat) : Fp) := by
      show Expression.eval env (inp.r + sc nFp (seedPhase inp n).1.overflow) = _
      rw [eval_r_plus_overflow]
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rw [hRX]
    exact (x_mod_order_iff_lift hrv_lt hovv hrn).2


theorem eval_pm_var (env : Environment Fp) (a : E) (i : Nat) :
    Expression.eval env (pm a (var ⟨i⟩)) = Expression.eval env a * env.get i := rfl

theorem getD_eq_default {v : Vector E 256} {k : Nat} (hk : ¬ k < 256) :
    v.getD k (cst 0) = cst 0 := by
  simp only [Vector.getD, Vector.get, Array.getD, v.size_toArray, hk, dif_neg,
    not_false_eq_true]

theorem lit_nFp :
    (115792089210356248762697446949407573529996955224135760342422259061068512044369 : Fp)
      = (Challenge.Specs.ECDSAP256.n : Fp) := rfl

theorem seedPhase_complete (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((seedPhase inp n).2))
    (hov : Expression.eval env (seedPhase inp n).1.overflow = 0 ∨
           Expression.eval env (seedPhase inp n).1.overflow = 1) :
    ConstraintsHold.Completeness env ((seedPhase inp n).2) := by
  simp only [seedPhase, hint, Gadgets.assertBool, circuit_norm,
    Operations.localLength, Nat.add_zero] at hw hov ⊢
  rcases hov with h | h <;> rw [h] <;> ring

theorem nonzeroPhase_complete (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((nonzeroPhase inp n).2))
    (hr : Expression.eval env inp.r ≠ 0)
    (ht : Expression.eval env (cst (Challenge.Specs.ECDSAP256.n : Fp) - inp.s) ≠ 0) :
    ConstraintsHold.Completeness env ((nonzeroPhase inp n).2) := by
  simp only [nonzeroPhase, nonzero, circuit_norm, Operations.localLength,
    Nat.add_zero] at hw ⊢
  obtain ⟨h1, h2⟩ := hw
  have hr' : (ProvableStruct.eval env.toEnvironment inp).r = Expression.eval env.toEnvironment inp.r := by simp
  have hs' : (ProvableStruct.eval env.toEnvironment inp).s = Expression.eval env.toEnvironment inp.s := by simp
  refine ⟨?_, ?_⟩
  · rw [eval_pm_var, h1, hr', eval_cst]
    exact sub_eq_zero.mpr (mul_inv_cancel₀ hr)
  · rw [eval_pm_var, h2, hs']
    simp only [eval_sub, eval_cst, lit_nFp] at ht ⊢
    exact sub_eq_zero.mpr (mul_inv_cancel₀ ht)

theorem isOnCurve_complete (x y : E) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((isOnCurve x y).operations n))
    (hcurve : Expression.eval env.toEnvironment y ^ 2
      = Expression.eval env.toEnvironment x ^ 3 + pa * Expression.eval env.toEnvironment x + pb) :
    ConstraintsHold.Completeness env ((isOnCurve x y).operations n) := by
  simp only [isOnCurve, mm, bind_snd, Circuit.operations] at hw ⊢
  rw [ulwc_append] at hw
  obtain ⟨hA, hB⟩ := hw
  rw [ConstraintsHold.Completeness, Operations.forAllNoOffset_append]
  refine ⟨?_, ?_⟩
  · rw [mat_operations_eq] at hA ⊢
    exact mat_complete _ n env hA
  · refine assertZeroLazy_complete _ _ env ?_ ?_
    · rw [mat_operations_eq] at hB ⊢
      exact hB
    · have hmat : Expression.eval env.toEnvironment ((mat (.mul x x) n).1)
          = Expression.eval env.toEnvironment x * Expression.eval env.toEnvironment x := by
        rw [mat_output_eq]
        exact matOut_eval_complete env _ n (by rwa [mat_operations_eq] at hA)
      simp only [sc, cst, eval_add', eval_mul, eval_neg, eval_sub, eval_cst, eval_const, hmat]
      linear_combination hcurve

theorem curvePhase_complete (inp : Var Input Fp) (s : Seed) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((curvePhase inp s n).2))
    (h1 : Expression.eval env.toEnvironment inp.pkY ^ 2
      = Expression.eval env.toEnvironment inp.pkX ^ 3 + pa * Expression.eval env.toEnvironment inp.pkX + pb)
    (h2 : Expression.eval env.toEnvironment s.ry ^ 2
      = Expression.eval env.toEnvironment (inp.r + sc nFp s.overflow) ^ 3
        + pa * Expression.eval env.toEnvironment (inp.r + sc nFp s.overflow) + pb)
    (h3 : Expression.eval env.toEnvironment s.hy ^ 2
      = Expression.eval env.toEnvironment s.hx ^ 3 + pa * Expression.eval env.toEnvironment s.hx + pb) :
    ConstraintsHold.Completeness env ((curvePhase inp s n).2) := by
  simp only [curvePhase, bind_snd, Circuit.operations] at hw ⊢
  simp only [ulwc_append, Operations.append_localLength, ← Nat.add_assoc] at hw
  obtain ⟨⟨hA, hB⟩, hC⟩ := hw
  simp only [ConstraintsHold.Completeness, Operations.forAllNoOffset_append]
  exact ⟨⟨isOnCurve_complete _ _ env n hA h1,
    isOnCurve_complete _ _ env _ hB h2⟩,
    isOnCurve_complete _ _ env _ hC h3⟩

theorem bitBody_complete (base stride : Nat) (i : Fin 256) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((bitBody base stride i).operations n))
    (hb : Expression.eval env.toEnvironment ((bitBody base stride i).output n) = 0 ∨
          Expression.eval env.toEnvironment ((bitBody base stride i).output n) = 1) :
    ConstraintsHold.Completeness env ((bitBody base stride i).operations n) := by
  simp only [bitBody, hint, Gadgets.assertBool, circuit_norm, Operations.localLength,
    Nat.add_zero] at hw hb ⊢
  rcases hb with h | h <;> rw [h] <;> ring

theorem bitVec_complete (base stride : Nat) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((bitVec base stride).operations n))
    (hb : ∀ k : Fin 256,
      Expression.eval env.toEnvironment (((bitVec base stride).output n).get k) = 0 ∨
      Expression.eval env.toEnvironment (((bitVec base stride).output n).get k) = 1) :
    ConstraintsHold.Completeness env ((bitVec base stride).operations n) := by
  simp only [bitVec, ConstraintsHold.Completeness, Circuit.mapFinRange.forAll',
    Circuit.mapFinRange.usesLocalWitnesses] at hw ⊢
  intro i
  refine bitBody_complete base stride i env _ (hw i) ?_
  have hbi := hb i
  rw [bitVec, Circuit.mapFinRange.output_eq] at hbi
  simpa only [Vector.getElem_mapFinRange, Vector.get_eq_getElem, bitBody_localLength,
    Nat.mul_one] using hbi

theorem bitsPhase_complete (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((bitsPhase n).2))
    (hb : ∀ k : Fin 256, Expression.eval env.toEnvironment ((bitsPhase n).1.eb.get k) = 0 ∨
      Expression.eval env.toEnvironment ((bitsPhase n).1.eb.get k) = 1)
    (hb' : ∀ k : Fin 256, Expression.eval env.toEnvironment ((bitsPhase n).1.rb.get k) = 0 ∨
      Expression.eval env.toEnvironment ((bitsPhase n).1.rb.get k) = 1)
    (hb'' : ∀ k : Fin 256, Expression.eval env.toEnvironment ((bitsPhase n).1.sb.get k) = 0 ∨
      Expression.eval env.toEnvironment ((bitsPhase n).1.sb.get k) = 1) :
    ConstraintsHold.Completeness env ((bitsPhase n).2) := by
  simp only [bitsPhase, bind_snd, Circuit.operations] at hw ⊢
  simp only [ulwc_append, Operations.append_localLength, ← Nat.add_assoc] at hw
  obtain ⟨⟨hA, hB⟩, hC⟩ := hw
  simp only [ConstraintsHold.Completeness, Operations.forAllNoOffset_append]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact bitVec_complete 4 3 env n hA hb
  · exact bitVec_complete 5 3 env _ hB hb'
  · exact bitVec_complete 6 3 env _ hC hb''

theorem bindPhase_complete (inp : Var Input Fp) (b : Bits) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((bindPhase inp b n).2))
    (h0 : Expression.eval env (linComb b.eb 0 128) = Expression.eval env inp.digestLo)
    (h1 : Expression.eval env (linComb b.eb 128 128) = Expression.eval env inp.digestHi)
    (h2 : Expression.eval env (linComb b.rb 0 256) = Expression.eval env inp.r)
    (h3 : Expression.eval env (linComb b.sb 0 256)
      = Expression.eval env (cst (Challenge.Specs.ECDSAP256.n : Fp) - inp.s)) :
    ConstraintsHold.Completeness env ((bindPhase inp b n).2) := by
  simp only [bindPhase, Circuit.assertZero, circuit_norm, Operations.localLength,
    Nat.add_zero] at hw ⊢
  have hd : (ProvableStruct.eval env.toEnvironment inp).digestLo
      = Expression.eval env.toEnvironment inp.digestLo := by simp
  have hd' : (ProvableStruct.eval env.toEnvironment inp).digestHi
      = Expression.eval env.toEnvironment inp.digestHi := by simp
  have hr : (ProvableStruct.eval env.toEnvironment inp).r
      = Expression.eval env.toEnvironment inp.r := by simp
  have hs' : (ProvableStruct.eval env.toEnvironment inp).s
      = Expression.eval env.toEnvironment inp.s := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h0, hd, sub_self]
  · rw [h1, hd', sub_self]
  · rw [h2, hr, sub_self]
  · rw [h3]
    simp only [eval_sub, eval_cst, lit_nFp, hs', sub_self]

theorem assertLtOrderOf_complete (bound : Nat) (a : Nat → E) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((assertLtOrderOf bound a).operations n))
    (hpref : prefVal (boundNat bound) 256 = bound)
    (hcover : RunsCover bound 256 (boundRunsOf bound))
    (hb : ∀ k, Expression.eval env.toEnvironment (a k) = 0 ∨
      Expression.eval env.toEnvironment (a k) = 1)
    (hle : prefVal (fun j => aNatOf (fun k => Expression.eval env.toEnvironment (a k))
      (255 - j)) 256 ≤ bound) :
    ConstraintsHold.Completeness env ((assertLtOrderOf bound a).operations n) := by
  simp only [assertLtOrderOf] at hw ⊢
  refine ltLoop_complete env _ a (fun k => rfl) hb bound hpref hle
    (boundRunsOf bound) 256 (cst 0) n (by omega) hcover ?_ hw
  simp only [cst, eval_const]
  unfold missAbove
  simp

theorem assertLtOrderGuardedOf_complete (bound : Nat) (guard : E) (a : Nat → E)
    (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((assertLtOrderGuardedOf bound guard a).operations n))
    (hpref : prefVal (boundNat bound) 256 = bound)
    (hcover : RunsCover bound 256 (boundRunsOf bound))
    (hb : ∀ k, Expression.eval env.toEnvironment (a k) = 0 ∨
      Expression.eval env.toEnvironment (a k) = 1)
    (hg : Expression.eval env.toEnvironment guard = 0 ∨
      Expression.eval env.toEnvironment guard = 1)
    (hle : Expression.eval env.toEnvironment guard = 1 →
      prefVal (fun j => aNatOf (fun k => Expression.eval env.toEnvironment (a k))
        (255 - j)) 256 ≤ bound) :
    ConstraintsHold.Completeness env ((assertLtOrderGuardedOf bound guard a).operations n) := by
  simp only [assertLtOrderGuardedOf] at hw ⊢
  refine ltLoopGuarded_complete env _ a (fun k => rfl) hb bound guard hg hpref hle
    (boundRunsOf bound) 256 (cst 0) n (by omega) hcover ?_ hw
  simp only [cst, eval_const]
  unfold missAbove
  simp

theorem cmpPhase_complete (b : Bits) (overflow : E) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((cmpPhase b overflow n).2))
    (hb : ∀ k : Fin 256, Expression.eval env.toEnvironment (b.rb.get k) = 0 ∨
      Expression.eval env.toEnvironment (b.rb.get k) = 1)
    (hb' : ∀ k : Fin 256, Expression.eval env.toEnvironment (b.sb.get k) = 0 ∨
      Expression.eval env.toEnvironment (b.sb.get k) = 1)
    (hg : Expression.eval env.toEnvironment overflow = 0 ∨
      Expression.eval env.toEnvironment overflow = 1)
    (hle : prefVal (fun j => aNatOf (fun k => Expression.eval env.toEnvironment
      (b.rb.getD k (cst 0))) (255 - j)) 256 ≤ nSubOne)
    (hle' : prefVal (fun j => aNatOf (fun k => Expression.eval env.toEnvironment
      (b.sb.getD k (cst 0))) (255 - j)) 256 ≤ nSubOne)
    (hleg : Expression.eval env.toEnvironment overflow = 1 →
      prefVal (fun j => aNatOf (fun k => Expression.eval env.toEnvironment
        (b.rb.getD k (cst 0))) (255 - j)) 256 ≤ pSubNSubOne) :
    ConstraintsHold.Completeness env ((cmpPhase b overflow n).2) := by
  simp only [cmpPhase, bind_snd, Circuit.operations] at hw ⊢
  simp only [ulwc_append, Operations.append_localLength, ← Nat.add_assoc] at hw
  obtain ⟨⟨hA, hB⟩, hC⟩ := hw
  simp only [ConstraintsHold.Completeness, Operations.forAllNoOffset_append]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact assertLtOrderOf_complete nSubOne _ env n hA prefVal_boundNat_n runsCover_n
      (fun k => by
        by_cases hk : k < 256
        · rw [getD_eq_get hk]; exact hb ⟨k, hk⟩
        · rw [getD_eq_default hk]; simp) hle
  · exact assertLtOrderOf_complete nSubOne _ env _ hB prefVal_boundNat_n runsCover_n
      (fun k => by
        by_cases hk : k < 256
        · rw [getD_eq_get hk]; exact hb' ⟨k, hk⟩
        · rw [getD_eq_default hk]; simp) hle'
  · exact assertLtOrderGuardedOf_complete pSubNSubOne overflow _ env _ hC
      prefVal_boundNat_pn runsCover_pn
      (fun k => by
        by_cases hk : k < 256
        · rw [getD_eq_get hk]; exact hb ⟨k, hk⟩
        · rw [getD_eq_default hk]; simp) hg hleg


theorem affAdd_complete (p q : Pt) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((affAdd p q).operations n))
    (hDx : Expression.eval env.toEnvironment q.1 - Expression.eval env.toEnvironment p.1 ≠ 0) :
    ConstraintsHold.Completeness env ((affAdd p q).operations n) := by
  simp only [affAdd, nonzero, circuit_norm, pm] at hw ⊢
  obtain ⟨e1, e2, e3, e4⟩ := hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1]; simp only [eval_cst]; linear_combination mul_inv_cancel₀ hDx
  · rw [e2, e1]; field_simp; ring
  · rw [e3]; ring
  · rw [e4]; ring

theorem affDouble_complete (p : Pt) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((affDouble p).operations n))
    (hy : Expression.eval env.toEnvironment p.2 ≠ 0) :
    ConstraintsHold.Completeness env ((affDouble p).operations n) := by
  simp only [affDouble, mm, circuit_norm, pm] at hw ⊢
  obtain ⟨e1, e2, e3, e4⟩ := hw
  rw [mat_operations_eq] at e1
  have hlen : Operations.localLength (mat (.mul p.1 p.1) n).2 = matLen (.mul p.1 p.1) :=
    mat_localLength_eq _ n
  simp only [hlen] at e2 e3 e4 ⊢
  rw [Nat.add_comm (matLen (.mul p.1 p.1)) n] at e2 e3 e4
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mat_operations_eq]
    exact mat_complete _ n env e1
  · have h2 : (2 : Fp) ≠ 0 := by decide
    rw [e2]
    field_simp
    ring
  · rw [e3]; ring
  · rw [e4]; ring

end StandardECDSA
