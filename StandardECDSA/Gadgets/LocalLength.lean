/-
# Offset-free local lengths of the field gadgets

`Circuit.ConstantLength` for the phase loops needs the number of wires each
gadget allocates, independent of the offset.  This module proves those numbers
for `nonzero`, `affAdd`, `affDouble`, `elmCore`, `elm`, `elmTo`, `sel`,
`muxConst4` and `mux4`.

Task T05 / T10 / T12 (cost half).
-/

import StandardECDSA.Gadgets.Cost
import StandardECDSA.Gadgets.MatExplicit

namespace StandardECDSA.Gadgets

open Challenge.Instances.ECDSA_P256_Digest.Interface

theorem localLength_witness (m : Nat) (c : Witgen.WitgenIR Fp m) :
    Operations.localLength [Operation.witness m c] = m := rfl

theorem localLength_assert (e : E) : Operations.localLength [Operation.assert e] = 0 := rfl

/-! ## `matLen` vanishes on affine expressions -/

theorem matLen_eq_zero_of_deg_le_one {e : E} (h : deg e ≤ 1) : matLen e = 0 := by
  induction e with
  | var v => rfl
  | const c => rfl
  | add a b iha ihb =>
      have h' : max (deg a) (deg b) ≤ 1 := h
      simp only [matLen]
      rw [iha (by omega), ihb (by omega)]
  | mul a b iha ihb =>
      have h' : deg a + deg b ≤ 1 := h
      simp only [matLen]
      by_cases hz : deg a = 0 ∨ deg b = 0
      · rw [if_pos hz, iha (by omega), ihb (by omega)]
      · rw [if_neg hz]; omega

/-- A product of two affine non-constant expressions allocates exactly one wire. -/
theorem matLen_mul_of_deg_one {a b : E} (ha : deg a = 1) (hb : deg b = 1) :
    matLen (.mul a b) = 1 := by
  have h1 : matLen a = 0 := matLen_eq_zero_of_deg_le_one (by omega)
  have h2 : matLen b = 0 := matLen_eq_zero_of_deg_le_one (by omega)
  simp [matLen, ha, hb, h1, h2]

/-! ## Gadget local lengths -/

theorem nonzero_localLength (x : E) : ∀ n, (nonzero x).localLength n = 1 := by
  intro n
  simp only [nonzero, Circuit.localLength, bind_snd, pure_snd, witnessField_snd,
    assertZero_snd, localLength_witness, localLength_assert,
    Operations.append_localLength, Operations.localLength, Nat.add_zero, Nat.zero_add]

theorem affAdd_localLength (p q : Pt) : ∀ n, (affAdd p q).localLength n = 4 := by
  intro n
  simp only [affAdd, Circuit.localLength, bind_snd, pure_snd, witnessField_snd,
    assertZero_snd, localLength_witness, localLength_assert,
    Operations.append_localLength, Operations.localLength, nonzero_localLength,
    Nat.add_zero, Nat.zero_add]

theorem affDouble_localLength {p : Pt} (hx : deg p.1 = 1) :
    ∀ n, (affDouble p).localLength n = 4 := by
  intro n
  have hml : matLen (.mul p.1 p.1) = 1 := matLen_mul_of_deg_one hx hx
  simp only [affDouble, Circuit.localLength, bind_snd, pure_snd, witnessField_snd,
    assertZero_snd, localLength_witness, localLength_assert,
    Operations.append_localLength, Operations.localLength, mm, mat_localLength_eq, hml,
    Nat.add_zero, Nat.zero_add]

theorem elmCore_localLength (p q : Pt) : ∀ n, (elmCore p q).localLength n = 4 := by
  intro n
  simp only [elmCore, Circuit.localLength, bind_snd, pure_snd, witnessField_snd,
    assertZero_snd, localLength_witness, localLength_assert,
    Operations.append_localLength, Operations.localLength, nonzero_localLength,
    Nat.add_zero, Nat.zero_add]

theorem elm_localLength (p q : Pt) : ∀ n, (elm p q).localLength n = 6 := by
  intro n
  simp only [elm, Circuit.localLength, bind_snd, pure_snd, witnessField_snd,
    assertZero_snd, localLength_witness, localLength_assert,
    Operations.append_localLength, Operations.localLength, elmCore_localLength,
    Nat.add_zero, Nat.zero_add]

theorem elmTo_localLength (p q target : Pt) : ∀ n, (elmTo p q target).localLength n = 4 := by
  intro n
  simp only [elmTo, Circuit.localLength, bind_snd, pure_snd, witnessField_snd,
    assertZero_snd, localLength_witness, localLength_assert,
    Operations.append_localLength, Operations.localLength, elmCore_localLength,
    Nat.add_zero, Nat.zero_add]

theorem sel_localLength {b x0 x1 : E} (hb : deg b = 1) (h0 : deg x0 = 1) (h1 : deg x1 = 1) :
    ∀ n, (sel b x0 x1).localLength n = 1 := by
  intro n
  have hsub : deg (x1 - x0) = 1 := by
    show max (deg x1) (deg (Expression.mul (Expression.const (-1)) x0)) = 1
    rw [show deg (Expression.mul (Expression.const (-1)) x0) = 0 + deg x0 from rfl, h0, h1]
    rfl
  have hml : matLen (.mul b (x1 - x0)) = 1 := matLen_mul_of_deg_one hb hsub
  have hx0 : matLen x0 = 0 := matLen_eq_zero_of_deg_le_one (by rw [h0])
  have hsum : matLen (x0 + .mul b (x1 - x0)) = 1 := by
    have h2 := hml
    simp only [matLen] at h2 ⊢
    rw [hx0, h2]
  simp only [sel, Circuit.localLength, bind_snd, pure_snd, witnessField_snd,
    assertZero_snd, localLength_witness, localLength_assert,
    Operations.append_localLength, Operations.localLength, mat_localLength_eq, hsum,
    Nat.add_zero, Nat.zero_add]

theorem muxConst4_localLength {b0 b1 : E} (h0 : deg b0 = 1) (h1 : deg b1 = 1)
    (tab : Array (Fp × Fp)) : ∀ n, (muxConst4 b0 b1 tab).localLength n = 1 := by
  intro n
  have hml : matLen (.mul b0 b1) = 1 := matLen_mul_of_deg_one h0 h1
  simp only [muxConst4, Circuit.localLength, bind_snd, pure_snd, witnessField_snd,
    assertZero_snd, localLength_witness, localLength_assert,
    Operations.append_localLength, Operations.localLength, mm, mat_localLength_eq, hml,
    Nat.add_zero, Nat.zero_add]

theorem mux4_localLength {b0 b1 : E} (hb0 : deg b0 = 1) (hb1 : deg b1 = 1)
    {p0 p1 p2 p3 : Pt}
    (h0 : deg p0.1 = 1 ∧ deg p0.2 = 1) (h1 : deg p1.1 = 1 ∧ deg p1.2 = 1)
    (h2 : deg p2.1 = 1 ∧ deg p2.2 = 1) (h3 : deg p3.1 = 1 ∧ deg p3.2 = 1) :
    ∀ n, (mux4 b0 b1 p0 p1 p2 p3).localLength n = 6 := by
  intro n
  have hax : ∀ m, deg (Circuit.output (sel b0 p0.1 p1.1) m) = 1 := (sel_cost hb0 h0.1 h1.1).2
  have hbx : ∀ m, deg (Circuit.output (sel b0 p2.1 p3.1) m) = 1 := (sel_cost hb0 h2.1 h3.1).2
  have hay : ∀ m, deg (Circuit.output (sel b0 p0.2 p1.2) m) = 1 := (sel_cost hb0 h0.2 h1.2).2
  have hby : ∀ m, deg (Circuit.output (sel b0 p2.2 p3.2) m) = 1 := (sel_cost hb0 h2.2 h3.2).2
  simp only [mux4, Circuit.localLength, Circuit.output, bind_snd, pure_snd,
    witnessField_snd, assertZero_snd, localLength_witness, localLength_assert,
    Operations.append_localLength, Operations.localLength, sel_localLength,
    hb0, hb1, h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, hax, hbx, hay, hby,
    Nat.add_zero, Nat.zero_add]

end StandardECDSA.Gadgets
