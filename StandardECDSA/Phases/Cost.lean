/-
# Phase cost certificates

Exact allocation/row counts for the three phases, composed from the per-gadget
`CostIs` lemmas in `StandardECDSA.Gadgets.Cost` via `CostIs.bind` and
`CostIs.foldlRange`.

| Phase | Allocations | Rows |
|---|---:|---:|
| `fixedBase` | 644 | 644 |
| `shiftedTables` | 32 | 32 |
| `jointLadder` | 3,070 | 3,072 |

Task T12 / T15 / T18.
-/

import StandardECDSA.Gadgets.LocalLength
import StandardECDSA.Phases.FixedBase
import StandardECDSA.Phases.ShiftedTables
import StandardECDSA.Phases.JointLadder

namespace StandardECDSA.Phases

open StandardECDSA.Gadgets
open Challenge.CostR1CS

/-! ## Fixed base -/

/-- One window of the fixed-base phase costs `muxConst4` (1/1) plus `affAdd`
(4/4). -/
theorem fixedBaseBody_cost (eb : Vector E 256) (tables : Array (Array (Fp × Fp)))
    (ep : Pt) (i : Fin 128) :
    CostIs (fixedBaseBody eb tables ep i) ⟨5, 5⟩ := by
  have h := CostIs.bind
    (muxConst4W_cost (eb.get ⟨2 * i.val, by omega⟩)
      (eb.get ⟨2 * i.val + 1, by omega⟩) (tables.getD i.val #[]))
    (fun t => affAdd_cost ep t)
  exact h

/-- The fixed-base phase costs `affAdd` (4/4) plus 128 windows of 5/5. -/
theorem fixedBase_cost (h : Pt) (eb : Vector E 256) :
    CostIs (fixedBase h eb) ⟨644, 644⟩ := by
  intro n
  have hfb := CostIs.foldlRange (m := 128)
    (init := (affAdd h (cst shiftX, cst (-shiftY)) n).1)
    (body := fixedBaseBody eb StandardECDSA.Math.FixedTables.fixedTables)
    (constant := fixedBaseBody_constantLength eb StandardECDSA.Math.FixedTables.fixedTables)
    (K := ⟨5, 5⟩) (fun s i n => fixedBaseBody_cost eb _ s i n)
  simp only [fixedBase, Circuit.operations, affAdd_localLength]
  rw [Challenge.CostR1CS.Lemmas.operationCount_append, affAdd_cost h _ n, hfb]
  decide

/-! ## Shifted tables -/

/-- Building both shifted tables costs `affDouble` (4/4) plus seven `affAdd`
(28/28). -/
theorem shiftedTables_cost (h q r : Pt) (hh : deg h.1 = 1) :
    CostIs (shiftedTables h q r) ⟨32, 32⟩ := by
  have h1 : CostIs (shiftedTables h q r)
      (⟨4, 4⟩ + (⟨4, 4⟩ + (⟨4, 4⟩ + (⟨4, 4⟩ + (⟨4, 4⟩ + (⟨4, 4⟩ + (⟨4, 4⟩ +
        (⟨4, 4⟩ + Count.zero)))))))) :=
    CostIs.bind (affDouble_cost (p := h) hh) (fun hh2 =>
      CostIs.bind (affAdd_cost hh2 h) (fun hhh =>
        CostIs.bind (affAdd_cost hhh q) (fun p1 =>
          CostIs.bind (affAdd_cost hhh r) (fun p2 =>
            CostIs.bind (affAdd_cost p1 r) (fun p3 =>
              CostIs.bind (affAdd_cost (negPt hhh) q) (fun m1 =>
                CostIs.bind (affAdd_cost (negPt hhh) r) (fun m2 =>
                  CostIs.bind (affAdd_cost m1 r) (fun m3 =>
                    CostIs.pure _))))))))
  exact CostIs.congr h1 (by decide)

/-! ## Joint ladder -/

/-- One returning ladder step costs `mux4` (6/6) plus `elm` (6/6). -/
theorem jointLadderBody_cost (tables : Tables) (rb sb : Vector E 256) (acc : Pt) (j : Fin 255) :
    CostIs (jointLadderBody tables rb sb acc j) ⟨12, 12⟩ := by
  have h := CostIs.bind
    (mux4W_cost (rb.get ⟨255 - j.val, by omega⟩) (sb.get ⟨255 - j.val, by omega⟩)
      (tables.x0 j.val) (tables.x1 j.val) (tables.x2 j.val) (tables.x3 j.val))
    (fun t => elm_cost acc t)
  exact h

/-- The final ladder step costs `mux4` (6/6) plus `elmTo` (4/6). -/
theorem jointLadderFinal_cost (tables : Tables) (rb sb : Vector E 256) (acc target : Pt) :
    CostIs (jointLadderFinal tables rb sb acc target) ⟨10, 12⟩ := by
  have h := CostIs.bind
    (mux4W_cost (rb.get ⟨0, by omega⟩) (sb.get ⟨0, by omega⟩)
      (tables.x0 255) (tables.x1 255) (tables.x2 255) (tables.x3 255))
    (fun t => elmTo_cost acc t target)
  exact h

/-- The joint ladder costs 255 returning steps of 12/12 plus a final 10/12. -/
theorem jointLadder_cost (acc0 : Pt) (tables : Tables) (rb sb : Vector E 256) (target : Pt) :
    CostIs (jointLadder acc0 tables rb sb target) ⟨3070, 3072⟩ := by
  have h1 : CostIs (jointLadder acc0 tables rb sb target)
      (⟨255 * 12, 255 * 12⟩ + ⟨10, 12⟩) :=
    CostIs.bind
      (CostIs.foldlRange (m := 255) (init := acc0)
        (body := jointLadderBody tables rb sb)
        (constant := jointLadderBody_constantLength tables rb sb)
        (K := ⟨12, 12⟩) (fun s i n => jointLadderBody_cost tables rb sb s i n))
      (fun acc => jointLadderFinal_cost tables rb sb acc target)
  exact CostIs.congr h1 (by decide)

end StandardECDSA.Phases
