/-
# Degree-free multiplexers

`sel`, `muxConst4` and `mux4` route their products through `mat`, whose
allocation count branches on `deg a = 0 ∨ deg b = 0`.  For *opaque* selector
expressions that branch is not decidable at elaboration time, so the
`localLength` of those gadgets — and hence the `ConstantLength` instance needed
by `Circuit.foldlRange` — is stuck.

Plan §6 T05 requires "explicit operations whose counts do not depend on
syntactic constant-folding branches in arbitrary inputs".  The `…W` variants
below satisfy that: they always allocate the product wire and always emit the
product row, so their `localLength` is a literal constant with no degree
hypothesis.  When the selectors are genuine wires (degree one) they are
row-for-row identical to `sel`/`muxConst4`/`mux4`, so the measured cost is
unchanged.

Task T05 / T10.
-/

import StandardECDSA.Gadgets.Select
import StandardECDSA.Gadgets.LocalLength
import StandardECDSA.Gadgets.R1CS

namespace StandardECDSA.Gadgets

/-- Degree-free two-way select: `x0` if `b = 0`, `x1` if `b = 1`.
One allocation, one row, constant length. -/
def selW (b x0 x1 : E) : C E := do
  let w ← Circuit.witnessField (.mul (.expr b) (.expr (x1 - x0)))
  Circuit.assertZero (pm b (x1 - x0) - w)
  pure (x0 + w)

/-- Degree-free constant four-way point mux, indexed by `b0 + 2·b1`.
One allocation, one row, constant length. -/
def muxConst4W (b0 b1 : E) (tab : Array (Fp × Fp)) : C Pt := do
  let b01 ← Circuit.witnessField (.mul (.expr b0) (.expr b1))
  Circuit.assertZero (pm b0 b1 - b01)
  let coord (get : Fp × Fp → Fp) : E :=
    muxConst4Coord (get (tab.getD 0 (0, 0))) (get (tab.getD 1 (0, 0)))
      (get (tab.getD 2 (0, 0))) (get (tab.getD 3 (0, 0))) b0 b1 b01
  pure (coord Prod.fst, coord Prod.snd)

/-- Degree-free four-way variable point mux, indexed by `b0 + 2·b1`.
Six allocations, six rows, constant length. -/
def mux4W (b0 b1 : E) (p0 p1 p2 p3 : Pt) : C Pt := do
  let ax ← selW b0 p0.1 p1.1
  let bx ← selW b0 p2.1 p3.1
  let x ← selW b1 ax bx
  let ay ← selW b0 p0.2 p1.2
  let by' ← selW b0 p2.2 p3.2
  let y ← selW b1 ay by'
  return (x, y)

/-! ## Constant length -/

theorem selW_localLength (b x0 x1 : E) : ∀ n, (selW b x0 x1).localLength n = 1 := by
  intro n
  simp only [selW, Circuit.localLength, bind_snd, pure_snd, witnessField_snd,
    assertZero_snd, localLength_witness, localLength_assert,
    Operations.append_localLength, Operations.localLength, Nat.add_zero, Nat.zero_add]

theorem muxConst4W_localLength (b0 b1 : E) (tab : Array (Fp × Fp)) :
    ∀ n, (muxConst4W b0 b1 tab).localLength n = 1 := by
  intro n
  simp only [muxConst4W, Circuit.localLength, bind_snd, pure_snd, witnessField_snd,
    assertZero_snd, localLength_witness, localLength_assert,
    Operations.append_localLength, Operations.localLength, Nat.add_zero, Nat.zero_add]

theorem mux4W_localLength (b0 b1 : E) (p0 p1 p2 p3 : Pt) :
    ∀ n, (mux4W b0 b1 p0 p1 p2 p3).localLength n = 6 := by
  intro n
  simp only [mux4W, Circuit.localLength, bind_snd, pure_snd,
    selW_localLength, Operations.append_localLength, Operations.localLength,
    Nat.add_zero, Nat.zero_add]

/-! ## Cost -/

open Challenge.CostR1CS

theorem selW_cost (b x0 x1 : E) : CostIs (selW b x0 x1) ⟨1, 1⟩ := by
  have h : CostIs (selW b x0 x1) (⟨1, 0⟩ + (⟨0, 1⟩ + Count.zero)) := by
    simp only [selW]
    exact CostIs.bind (CostIs.witnessField _) (fun w =>
      CostIs.bind (CostIs.assertZero _) (fun _ => CostIs.pure _))
  exact CostIs.congr h rfl

theorem muxConst4W_cost (b0 b1 : E) (tab : Array (Fp × Fp)) :
    CostIs (muxConst4W b0 b1 tab) ⟨1, 1⟩ := by
  have h : CostIs (muxConst4W b0 b1 tab) (⟨1, 0⟩ + (⟨0, 1⟩ + Count.zero)) := by
    simp only [muxConst4W]
    exact CostIs.bind (CostIs.witnessField _) (fun b01 =>
      CostIs.bind (CostIs.assertZero _) (fun _ => CostIs.pure _))
  exact CostIs.congr h rfl

theorem mux4W_cost (b0 b1 : E) (p0 p1 p2 p3 : Pt) :
    CostIs (mux4W b0 b1 p0 p1 p2 p3) ⟨6, 6⟩ := by
  have h : CostIs (mux4W b0 b1 p0 p1 p2 p3)
      (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + (⟨1, 1⟩ + Count.zero)))))) := by
    simp only [mux4W]
    exact CostIs.bind (selW_cost _ _ _) (fun ax =>
      CostIs.bind (selW_cost _ _ _) (fun bx =>
        CostIs.bind (selW_cost _ _ _) (fun x =>
          CostIs.bind (selW_cost _ _ _) (fun ay =>
            CostIs.bind (selW_cost _ _ _) (fun by' =>
              CostIs.bind (selW_cost _ _ _) (fun y => CostIs.pure _))))))
  exact CostIs.congr h rfl

/-! ## Single-row R1CS -/

theorem isR1CSCirc_selW {b x0 x1 : E} (hb : deg b ≤ 1) (h0 : deg x0 ≤ 1)
    (h1 : deg x1 ≤ 1) : IsR1CSCirc (selW b x0 x1) := by
  have hd : deg (x1 - x0) ≤ 1 := by
    rw [show deg (x1 - x0) = max (deg x1) (deg x0) from Challenge.CostR1CS.degree_sub x1 x0]
    exact Nat.max_le.2 ⟨h1, h0⟩
  simp only [selW]
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) (fun n => ?_)
  refine IsR1CSCirc.bind_out (IsR1CSCirc.assertZero ?_) (fun _ => ?_)
  · exact isR1CSRow_prod_sub hb hd (deg_var_le n)
  exact IsR1CSCirc.pure _

theorem isR1CSCirc_muxConst4W {b0 b1 : E} (h0 : deg b0 ≤ 1) (h1 : deg b1 ≤ 1)
    (tab : Array (Fp × Fp)) : IsR1CSCirc (muxConst4W b0 b1 tab) := by
  simp only [muxConst4W]
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) (fun n => ?_)
  refine IsR1CSCirc.bind_out (IsR1CSCirc.assertZero ?_) (fun _ => ?_)
  · exact isR1CSRow_prod_sub h0 h1 (deg_var_le n)
  exact IsR1CSCirc.pure _

theorem isR1CSCirc_mux4W {b0 b1 : E} (hb0 : deg b0 ≤ 1) (hb1 : deg b1 ≤ 1)
    {p0 p1 p2 p3 : Pt}
    (h0 : deg p0.1 ≤ 1 ∧ deg p0.2 ≤ 1) (h1 : deg p1.1 ≤ 1 ∧ deg p1.2 ≤ 1)
    (h2 : deg p2.1 ≤ 1 ∧ deg p2.2 ≤ 1) (h3 : deg p3.1 ≤ 1 ∧ deg p3.2 ≤ 1) :
    IsR1CSCirc (mux4W b0 b1 p0 p1 p2 p3) := by
  have hax : deg (Circuit.output (selW b0 p0.1 p1.1) 0) ≤ 1 := by
    show deg (p0.1 + Expression.var (F := Fp) ⟨0⟩) ≤ 1
    rw [show deg (p0.1 + Expression.var (F := Fp) ⟨0⟩) =
      max (deg p0.1) (deg (Expression.var (F := Fp) ⟨0⟩)) from rfl]
    exact Nat.max_le.2 ⟨h0.1, deg_var_le 0⟩
  simp only [mux4W]
  refine IsR1CSCirc.bind_out (isR1CSCirc_selW hb0 h0.1 h1.1) (fun n => ?_)
  refine IsR1CSCirc.bind_out (isR1CSCirc_selW hb0 h2.1 h3.1) (fun n1 => ?_)
  refine IsR1CSCirc.bind_out (isR1CSCirc_selW hb1 ?_ ?_) (fun n2 => ?_)
  · show deg (Circuit.output (selW b0 p0.1 p1.1) n) ≤ 1
    exact hax
  · show deg (Circuit.output (selW b0 p2.1 p3.1) n1) ≤ 1
    show deg (p2.1 + Expression.var (F := Fp) ⟨n1⟩) ≤ 1
    rw [show deg (p2.1 + Expression.var (F := Fp) ⟨n1⟩) =
      max (deg p2.1) (deg (Expression.var (F := Fp) ⟨n1⟩)) from rfl]
    exact Nat.max_le.2 ⟨h2.1, deg_var_le n1⟩
  refine IsR1CSCirc.bind_out (isR1CSCirc_selW hb0 h0.2 h1.2) (fun n3 => ?_)
  refine IsR1CSCirc.bind_out (isR1CSCirc_selW hb0 h2.2 h3.2) (fun n4 => ?_)
  refine IsR1CSCirc.bind_out (isR1CSCirc_selW hb1 ?_ ?_) (fun n5 => ?_)
  · show deg (Circuit.output (selW b0 p0.2 p1.2) n3) ≤ 1
    show deg (p0.2 + Expression.var (F := Fp) ⟨n3⟩) ≤ 1
    rw [show deg (p0.2 + Expression.var (F := Fp) ⟨n3⟩) =
      max (deg p0.2) (deg (Expression.var (F := Fp) ⟨n3⟩)) from rfl]
    exact Nat.max_le.2 ⟨h0.2, deg_var_le n3⟩
  · show deg (Circuit.output (selW b0 p2.2 p3.2) n4) ≤ 1
    show deg (p2.2 + Expression.var (F := Fp) ⟨n4⟩) ≤ 1
    rw [show deg (p2.2 + Expression.var (F := Fp) ⟨n4⟩) =
      max (deg p2.2) (deg (Expression.var (F := Fp) ⟨n4⟩)) from rfl]
    exact Nat.max_le.2 ⟨h2.2, deg_var_le n4⟩
  exact IsR1CSCirc.pure _

end StandardECDSA.Gadgets
