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

end StandardECDSA
