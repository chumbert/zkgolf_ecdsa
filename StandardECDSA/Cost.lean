/-
# Whole-circuit cost certificate

`main_cost` certifies the exact allocation/row count of the assembled standard
P-256 ECDSA circuit: **4,628 allocations + 4,634 rows = 9,262**, matching the
plan's proposed budget exactly (no delta).

The certificate is compositional: `main_ops'` splits `main` into its nine
stages, `Lemmas.operationCount_append` splits the count, and each stage is
discharged by its own `CostIs` lemma.  The three arithmetic phases reuse the
certificates in `StandardECDSA.Phases.Cost`; the six scalar/curve phases are
certified here.

| Stage | Allocations | Rows |
|---|---:|---:|
| `seedPhase` | 4 | 1 |
| `curvePhase` | 6 | 9 |
| `nonzeroPhase` | 2 | 2 |
| `bitsPhase` | 768 | 768 |
| `bindPhase` | 0 | 4 |
| `cmpPhase` | 102 | 102 |
| `fixedBase` | 644 | 644 |
| `shiftedTables` | 32 | 32 |
| `jointLadder` | 3,070 | 3,072 |
| **total** | **4,628** | **4,634** |

Task T18.
-/

import StandardECDSA.Main
import StandardECDSA.Phases.Cost
import Challenge.Utils.CostR1CS

set_option maxRecDepth 100000

namespace StandardECDSA

open Challenge.CostR1CS
open StandardECDSA.Gadgets
open StandardECDSA.Phases

/-- The concrete input embedding: the six external inputs are wires `0 … 5`. -/
def inputVar : Var Input Fp :=
  { pkX := .var ⟨0⟩, pkY := .var ⟨1⟩, digestLo := .var ⟨2⟩, digestHi := .var ⟨3⟩,
    r := .var ⟨4⟩, s := .var ⟨5⟩ }

/-! ## Scalar and curve stages -/

/-- Stage 1 costs four hint cells and one Boolean row. -/
theorem seedPhase_cost (inp : Var Input Fp) : CostIs (seedPhase inp) ⟨4, 1⟩ := by
  intro n
  rfl

/-- Stage 3 costs two inverse witnesses and two rows. -/
theorem nonzeroPhase_cost (inp : Var Input Fp) : CostIs (nonzeroPhase inp) ⟨2, 2⟩ := by
  intro n
  rfl

/-- Stage 5 costs no allocation and four rows. -/
theorem bindPhase_cost (inp : Var Input Fp) (b : Bits) : CostIs (bindPhase inp b) ⟨0, 4⟩ := by
  intro n
  rfl

/-- One digest/scalar bit costs one cell and one Boolean row. -/
theorem bitBody_cost (base stride : Nat) (i : Fin 256) :
    CostIs (bitBody base stride i) ⟨1, 1⟩ := by
  intro n
  rfl

/-- A 256-bit hint vector costs 256 cells and 256 rows. -/
theorem bitVec_cost (base stride : Nat) : CostIs (bitVec base stride) ⟨256, 256⟩ := by
  have h := CostIs.mapFinRange (m := 256) (body := bitBody base stride)
    (constant := bitBody_constantLength base stride) (K := ⟨1, 1⟩)
    (fun i n => bitBody_cost base stride i n)
  exact CostIs.congr h (by decide)

/-- Stage 4 costs three 256-bit vectors: 768 cells and 768 rows. -/
theorem bitsPhase_cost : CostIs bitsPhase ⟨768, 768⟩ := by
  intro n
  have h0 := bitVec_cost 4 3 n
  have h1 := bitVec_cost 5 3 (n + Operations.localLength (bitVec 4 3 n).2)
  have h2 := bitVec_cost 6 3 (n + Operations.localLength (bitVec 4 3 n).2
    + Operations.localLength (bitVec 5 3 (n + Operations.localLength (bitVec 4 3 n).2)).2)
  simp only [bitsPhase, Circuit.operations, Lemmas.operationCount_append, h0, h1, h2]
  decide

/-- Stage 6 costs three 34/34 comparators: 102 cells and 102 rows. -/
theorem cmpPhase_cost (b : Bits) (overflow : E) : CostIs (cmpPhase b overflow) ⟨102, 102⟩ := by
  intro n
  have h0 := assertLtOrderOf_cost_n (fun i => b.rb.getD i (cst 0)) n
  have h1 := assertLtOrderOf_cost_n (fun i => b.sb.getD i (cst 0))
    (n + Operations.localLength ((assertLtOrderOf nSubOne (fun i => b.rb.getD i (cst 0)) n).2))
  have h2 := assertLtOrderGuardedOf_cost_p overflow (fun i => b.rb.getD i (cst 0))
    (n + Operations.localLength ((assertLtOrderOf nSubOne (fun i => b.rb.getD i (cst 0)) n).2)
      + Operations.localLength ((assertLtOrderOf nSubOne (fun i => b.sb.getD i (cst 0))
          (n + Operations.localLength
            ((assertLtOrderOf nSubOne (fun i => b.rb.getD i (cst 0)) n).2))).2))
  simp only [cmpPhase, Circuit.operations, Lemmas.operationCount_append, h0, h1, h2]
  decide

/-! ## The shifted on-curve assertion

`curvePhase`'s second assertion is `isOnCurve (r + n·overflow) ry`, whose first
coordinate is the affine expression `var vx + sc c (var vo)` rather than a bare
wire.  Its cost is still 2/3; the two lemmas below establish that.
-/

/-- `flat` of the on-curve expression when the first coordinate is
`var vx + sc c (var vo)`. -/
theorem flat_isOnCurve_shift (vx vo vy : Variable Fp) (c : Fp) (xx : E)
    (hxx : deg xx = 1) :
    flat 1 (.mul (.var vy) (.var vy)
        - (.mul (.var vx + sc c (.var vo)) xx + sc pa (.var vx + sc c (.var vo)) + cst pb))
      = [(1, .mul (.var vy) (.var vy)),
          (-1, .mul (.var vx + sc c (.var vo)) xx),
          (-1 * pa, .var vx), (-1 * pa * c, .var vo), (-1, .const pb)] := by
  have hxx' : Challenge.CostR1CS.degree xx = 1 := hxx
  change flat 1 (Expression.add (Expression.mul (.var vy) (.var vy))
    (Expression.mul (Expression.const (-1))
      (Expression.add (Expression.add
        (Expression.mul (Expression.add (.var vx) (Expression.mul (Expression.const c) (.var vo))) xx)
        (Expression.mul (Expression.const pa)
          (Expression.add (.var vx) (Expression.mul (Expression.const c) (.var vo)))))
        (Expression.const pb)))) = _
  simp only [flat, hxx', deg, Challenge.CostR1CS.degree, constVal, Expression.eval]
  rfl

/-- `isOnCurve` on `(var vx + sc c (var vo), var vy)` costs two allocations and
three rows. -/
theorem isOnCurve_cost_shift (vx vo vy : Variable Fp) (c : Fp) :
    CostIs (isOnCurve (.var vx + sc c (.var vo)) (.var vy)) ⟨2, 3⟩ := by
  have hmm := mm_spec (a := .var vx + sc c (.var vo)) (b := .var vx + sc c (.var vo)) rfl rfl
  have hdeg : deg (.var vx + sc c (.var vo)) = 1 := rfl
  have hmc : matCount (.var vx + sc c (.var vo)) = Count.zero := rfl
  have hazl : ∀ xx : E, deg xx = 1 → assertZeroLazyCost
      (.mul (.var vy) (.var vy)
        - (.mul (.var vx + sc c (.var vo)) xx + sc pa (.var vx + sc c (.var vo)) + cst pb))
      = ⟨1, 2⟩ := by
    intro xx hxx
    unfold assertZeroLazyCost
    rw [flat_isOnCurve_shift vx vo vy c xx hxx]
    simp only [List.filter, isProd, matCount, azlLoopCost, Count.zero, hxx, hdeg,
      matCount_eq_zero_of_deg_le_one (by omega : deg xx ≤ 1)]
    rfl
  have h : CostIs (mm (.var vx + sc c (.var vo)) (.var vx + sc c (.var vo)) >>= fun xx =>
      assertZeroLazy (.mul (.var vy) (.var vy)
        - (.mul (.var vx + sc c (.var vo)) xx + sc pa (.var vx + sc c (.var vo)) + cst pb)))
      (⟨1, 1⟩ + ⟨1, 2⟩) :=
    CostIs.bind_dep (P := fun xx => deg xx = 1) hmm.1
      (fun xx hx => CostIs.congr (assertZeroLazy_cost _) (hazl xx hx)) hmm.2
  exact CostIs.congr h rfl

/-- Stage 2 costs three on-curve assertions: 6 cells and 9 rows. -/
theorem curvePhase_cost (n : Nat) :
    operationCount ((curvePhase inputVar (seedPhase inputVar n).1 (off1 inputVar n)).2)
      = ⟨6, 9⟩ := by
  have h0 : operationCount ((isOnCurve inputVar.pkX inputVar.pkY (off1 inputVar n)).2)
      = ⟨2, 3⟩ := isOnCurve_cost_var ⟨0⟩ ⟨1⟩ (off1 inputVar n)
  have hl0 : Operations.localLength
      ((isOnCurve inputVar.pkX inputVar.pkY (off1 inputVar n)).2) = 2 := by rfl
  have h1 : operationCount ((isOnCurve (inputVar.r + sc nFp (seedPhase inputVar n).1.overflow)
      (seedPhase inputVar n).1.ry (off1 inputVar n + 2)).2) = ⟨2, 3⟩ :=
    isOnCurve_cost_shift ⟨4⟩ ⟨n + 1 + 1 + 1⟩ ⟨n⟩ nFp (off1 inputVar n + 2)
  have hl1 : Operations.localLength
      ((isOnCurve (inputVar.r + sc nFp (seedPhase inputVar n).1.overflow)
        (seedPhase inputVar n).1.ry (off1 inputVar n + 2)).2) = 2 := by rfl
  have h2 : operationCount ((isOnCurve (seedPhase inputVar n).1.hx
      (seedPhase inputVar n).1.hy (off1 inputVar n + 2 + 2)).2) = ⟨2, 3⟩ :=
    isOnCurve_cost_var ⟨n + 1⟩ ⟨n + 1 + 1⟩ (off1 inputVar n + 2 + 2)
  simp only [curvePhase, Lemmas.operationCount_append, h0, h1, h2, hl0, hl1]
  decide

/-! ## The whole circuit -/

/-- **Exact cost of the assembled circuit: 4,628 allocations + 4,634 rows.** -/
theorem main_cost : CostIs (main inputVar) ⟨4628, 4634⟩ := by
  intro n
  have h1 := seedPhase_cost inputVar n
  have h2 := curvePhase_cost n
  have h3 := nonzeroPhase_cost inputVar (off2 inputVar n)
  have h4 := bitsPhase_cost (off3 inputVar n)
  have h5 := bindPhase_cost inputVar (bitsPhase (off3 inputVar n)).1 (off4 inputVar n)
  have h6 := cmpPhase_cost (bitsPhase (off3 inputVar n)).1 (seedPhase inputVar n).1.overflow (off5 inputVar n)
  have h7 := fixedBase_cost ((seedPhase inputVar n).1.hx, (seedPhase inputVar n).1.hy)
    (bitsPhase (off3 inputVar n)).1.eb (off6 inputVar n)
  have h8 := shiftedTables_cost ((seedPhase inputVar n).1.hx, (seedPhase inputVar n).1.hy)
    (inputVar.pkX, inputVar.pkY)
    (inputVar.r + sc nFp (seedPhase inputVar n).1.overflow, (seedPhase inputVar n).1.ry)
    (seed_hx_deg inputVar n) (off7 inputVar n)
  have h9 := jointLadder_cost ((seedPhase inputVar n).1.hx, -(seedPhase inputVar n).1.hy)
    (shiftedTables ((seedPhase inputVar n).1.hx, (seedPhase inputVar n).1.hy)
      (inputVar.pkX, inputVar.pkY)
      (inputVar.r + sc nFp (seedPhase inputVar n).1.overflow, (seedPhase inputVar n).1.ry)
      (off7 inputVar n)).1
    (bitsPhase (off3 inputVar n)).1.rb (bitsPhase (off3 inputVar n)).1.sb
    (((fixedBase ((seedPhase inputVar n).1.hx, (seedPhase inputVar n).1.hy)
        (bitsPhase (off3 inputVar n)).1.eb (off6 inputVar n)).1).1,
      -((fixedBase ((seedPhase inputVar n).1.hx, (seedPhase inputVar n).1.hy)
        (bitsPhase (off3 inputVar n)).1.eb (off6 inputVar n)).1).2) (off8 inputVar n)
  rw [main_ops']
  simp only [Lemmas.operationCount_append, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  decide

end StandardECDSA
