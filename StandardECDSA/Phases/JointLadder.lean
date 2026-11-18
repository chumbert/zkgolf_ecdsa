/-
# Joint ladder phase

Ported from the pinned `circuit_baseline` revision
(`3a1bd20749ae0b6400a158651dba64a2c5fc58ff`), `Baseline/Projected/Offset.lean`.

The ladder consumes the scalar bits most-significant first (`index = 255 - j`)
and alternates the offset sign: `σ_j = -1` for even `j`, `+1` for odd `j`.
Before iteration `j`:

```text
C_0 = O
C_(j+1) = [2]C_j + T_j
T_j = [rBit[255-j]]Q + [tBit[255-j]]R
acc_j = C_j + [σ_j]H
selected_j = T_j - [3σ_j]H
acc_(j+1) = C_(j+1) - [σ_j]H
```

After 256 steps the represented point is `[r]Q + [t]R - H`.  The final step uses
`elmTo` to constrain the last output directly to `-ep`, giving exactly
`[E]G + [r]Q + [t]R = O` after cancelling `H`.

Cost: 255 × (`mux4` 6/6 + `elm` 6/6) + (`mux4` 6/6 + `elmTo` 4/6)
= 3,070 allocations and 3,072 rows.

Task T15.
-/

import StandardECDSA.Gadgets.ELM
import StandardECDSA.Gadgets.LocalLength
import StandardECDSA.Gadgets.SelectW
import StandardECDSA.Gadgets.Select
import StandardECDSA.Phases.ShiftedTables

namespace StandardECDSA.Phases

open StandardECDSA.Gadgets

/-- One returning ladder step: select `T_j` from the alternating table and
combine it with `[2]C_j` via `elm`.

Written as an explicit lambda rather than a `do` block so that
`(jointLadderBody ...).operations n` reduces to a `++` in one step; see the note
on `fixedBase` in `Phases/FixedBase.lean`. -/
def jointLadderBody (tables : Tables) (rb sb : Vector E 256) (acc : Pt) (j : Fin 255) : C Pt :=
  fun n =>
    let m := mux4W (rb.get ⟨255 - j.val, by omega⟩) (sb.get ⟨255 - j.val, by omega⟩)
      (tables.x0 j.val) (tables.x1 j.val) (tables.x2 j.val) (tables.x3 j.val) n
    let e := elm acc m.1 (n + Operations.localLength m.2)
    (e.1, m.2 ++ e.2)

/-- `jointLadderBody` is the `>>=`-composition of its two gadgets.

The cost certificate `jointLadderBody_cost` is stated for `>>=` (that is the
shape `CostIs.bind` produces), so it rewrites with this equation instead of
asking the elaborator to check the defeq directly. -/
theorem jointLadderBody_eq_bind (tables : Tables) (rb sb : Vector E 256) (acc : Pt)
    (j : Fin 255) :
    jointLadderBody tables rb sb acc j
      = (mux4W (rb.get ⟨255 - j.val, by omega⟩) (sb.get ⟨255 - j.val, by omega⟩)
          (tables.x0 j.val) (tables.x1 j.val) (tables.x2 j.val) (tables.x3 j.val)
          >>= fun t => elm acc t) := rfl

/-- Every returning ladder step allocates exactly twelve wires. -/
def jointLadderBody_constantLength (tables : Tables) (rb sb : Vector E 256) :
    Circuit.ConstantLength (fun (t : Pt × Fin 255) => jointLadderBody tables rb sb t.1 t.2) where
  localLength := 12
  localLength_eq := by
    intro t n
    obtain ⟨acc, j⟩ := t
    simp only [jointLadderBody, mux4W_localLength, elm_localLength, Circuit.localLength,
      Operations.append_localLength, Operations.localLength]

/-- The final ladder step: select `T_255` and assert the result equals `target`
via `elmTo`.  Explicit lambda, as for `jointLadderBody`. -/
def jointLadderFinal (tables : Tables) (rb sb : Vector E 256) (acc target : Pt) : C Unit :=
  fun n =>
    let m := mux4W (rb.get ⟨0, by omega⟩) (sb.get ⟨0, by omega⟩)
      (tables.x0 255) (tables.x1 255) (tables.x2 255) (tables.x3 255) n
    let e := elmTo acc m.1 target (n + Operations.localLength m.2)
    (e.1, m.2 ++ e.2)

/-- The joint ladder.  `acc0` is the initial accumulator `-H`; `rb`/`sb` hold the
`r` and `t = n - s` bits least significant first; `target` is `-ep`.

Explicit lambda, as for `jointLadderBody`. -/
def jointLadder (acc0 : Pt) (tables : Tables) (rb sb : Vector E 256) (target : Pt) :
    C Unit := fun n =>
  let r := Circuit.foldlRange 255 acc0 (jointLadderBody tables rb sb)
    (jointLadderBody_constantLength tables rb sb) n
  let e := jointLadderFinal tables rb sb r.1 target (n + Operations.localLength r.2)
  (e.1, r.2 ++ e.2)

/-! ## Per-step equation lemmas

These let parents reason about the ladder without ever unfolding the 255-step
fold or the `mux4W`/`elm` bodies. -/

/-- The 255-step fold allocates `255 * 12 = 3060` wires. -/
theorem jointLadderFold_localLength (acc0 : Pt) (tables : Tables) (rb sb : Vector E 256)
    (n : Nat) :
    (Circuit.foldlRange 255 acc0 (jointLadderBody tables rb sb)
      (jointLadderBody_constantLength tables rb sb)).localLength n = 3060 := by
  rw [Circuit.foldlRange.localLength_eq, dif_pos (by norm_num : (255 : Nat) > 0)]
  rw [(jointLadderBody_constantLength tables rb sb).localLength_eq
    (default, ⟨0, by norm_num⟩) 0]
  rfl

/-- The operations of one returning ladder step split into the `mux4W` and the
`elm`. -/
theorem jointLadderBody_ops (tables : Tables) (rb sb : Vector E 256) (acc : Pt)
    (j : Fin 255) (n : Nat) :
    (jointLadderBody tables rb sb acc j).operations n
      = (mux4W (rb.get ⟨255 - j.val, by omega⟩) (sb.get ⟨255 - j.val, by omega⟩)
            (tables.x0 j.val) (tables.x1 j.val) (tables.x2 j.val)
            (tables.x3 j.val)).operations n
        ++ (elm acc ((mux4W (rb.get ⟨255 - j.val, by omega⟩)
              (sb.get ⟨255 - j.val, by omega⟩)
              (tables.x0 j.val) (tables.x1 j.val) (tables.x2 j.val)
              (tables.x3 j.val)).output n)).operations (n + 6) := by
  simp only [jointLadderBody, Circuit.operations, Circuit.output, mux4W_localLength]

/-- The output of one returning ladder step is the `elm` output. -/
theorem jointLadderBody_out (tables : Tables) (rb sb : Vector E 256) (acc : Pt)
    (j : Fin 255) (n : Nat) :
    (jointLadderBody tables rb sb acc j).output n
      = (elm acc ((mux4W (rb.get ⟨255 - j.val, by omega⟩)
            (sb.get ⟨255 - j.val, by omega⟩)
            (tables.x0 j.val) (tables.x1 j.val) (tables.x2 j.val)
            (tables.x3 j.val)).output n)).output (n + 6) := by
  simp only [jointLadderBody, Circuit.operations, Circuit.output, mux4W_localLength]

/-- The operations of the final ladder step split into the `mux4W` and the
`elmTo`. -/
theorem jointLadderFinal_ops (tables : Tables) (rb sb : Vector E 256) (acc target : Pt)
    (n : Nat) :
    (jointLadderFinal tables rb sb acc target).operations n
      = (mux4W (rb.get ⟨0, by omega⟩) (sb.get ⟨0, by omega⟩)
            (tables.x0 255) (tables.x1 255) (tables.x2 255)
            (tables.x3 255)).operations n
        ++ (elmTo acc ((mux4W (rb.get ⟨0, by omega⟩) (sb.get ⟨0, by omega⟩)
              (tables.x0 255) (tables.x1 255) (tables.x2 255)
              (tables.x3 255)).output n) target).operations (n + 6) := by
  simp only [jointLadderFinal, Circuit.operations, Circuit.output, mux4W_localLength]

/-- The operations of the ladder split into the 255-step fold and the final step. -/
theorem jointLadder_ops (acc0 : Pt) (tables : Tables) (rb sb : Vector E 256)
    (target : Pt) (n : Nat) :
    (jointLadder acc0 tables rb sb target).operations n
      = (Circuit.foldlRange 255 acc0 (jointLadderBody tables rb sb)
            (jointLadderBody_constantLength tables rb sb)).operations n
        ++ (jointLadderFinal tables rb sb
              ((Circuit.foldlRange 255 acc0 (jointLadderBody tables rb sb)
                (jointLadderBody_constantLength tables rb sb)).output n)
              target).operations (n + 3060) := by
  simp only [jointLadder, Circuit.operations, Circuit.output, jointLadderFold_localLength]

/-- The output of the ladder is the output of the final step. -/
theorem jointLadder_out (acc0 : Pt) (tables : Tables) (rb sb : Vector E 256)
    (target : Pt) (n : Nat) :
    (jointLadder acc0 tables rb sb target).output n
      = (jointLadderFinal tables rb sb
            ((Circuit.foldlRange 255 acc0 (jointLadderBody tables rb sb)
              (jointLadderBody_constantLength tables rb sb)).output n)
            target).output (n + 3060) := by
  simp only [jointLadder, Circuit.operations, Circuit.output, jointLadderFold_localLength]

end StandardECDSA.Phases
