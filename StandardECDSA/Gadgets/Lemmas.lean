/-
# Field-level semantics of the standard circuit's gadgets

These lemmas are stated over an arbitrary field, independently of `Expression`
evaluation.  Each gadget's soundness proof reduces its rows to one of them.

A field bit `b` with `b = 0 ∨ b = 1` is written `(c.toNat : F)` for some
`c : Bool`.  Task T05/T10.
-/

import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace StandardECDSA.Gadgets

variable {K : Type*} [Field K]

/-- The Booleanity row `b * (b - 1) = 0` of `assertBool`. -/
theorem bool_iff (b : K) : b * (b - 1) = 0 ↔ b = 0 ∨ b = 1 := by
  rw [mul_eq_zero, sub_eq_zero]

/-- `bool_iff` with the constraint expanded as `b * b - b`. -/
theorem bool_iff' (b : K) : b * b - b = 0 ↔ b = 0 ∨ b = 1 := by
  rw [← bool_iff]; ring_nf

/-- A field bit is the image of a `Bool`. -/
theorem exists_bool_of_bit {b : K} (h : b = 0 ∨ b = 1) : ∃ c : Bool, b = c.toNat := by
  rcases h with rfl | rfl
  · exact ⟨false, by simp⟩
  · exact ⟨true, by simp⟩

/-- The nonzero row `x * x⁻¹ = 1` forces `x ≠ 0`. -/
theorem nonzero_spec {x inv : K} (h : x * inv - 1 = 0) : x ≠ 0 := by
  intro hx
  rw [hx, zero_mul, zero_sub] at h
  exact (neg_ne_zero.mpr one_ne_zero) h

/-- `sel b x0 x1` (`x0 + b * (x1 - x0)`) with a Boolean selector. -/
theorem sel_spec (c : Bool) (x0 x1 : K) :
    x0 + (c.toNat : K) * (x1 - x0) = if c then x1 else x0 := by
  cases c <;> simp

/-- The constant four-way mux `muxConst4`, with the shared bit product
`b01 = b0 * b1`.  Selects entry `b0 + 2 * b1`. -/
theorem muxConst4_spec (c0 c1 : Bool) (v0 v1 v2 v3 : K) :
    let b0 : K := c0.toNat
    let b1 : K := c1.toNat
    let b01 : K := b0 * b1
    v0 + (v1 - v0) * b0 + (v2 - v0) * b1 + (v3 - v2 - v1 + v0) * b01 =
      if c0 then (if c1 then v3 else v1) else (if c1 then v2 else v0) := by
  cases c0 <;> cases c1 <;> simp <;> ring

/-- The variable four-way mux `mux4`, indexed by `b0 + 2 * b1`. -/
theorem mux4_spec (c0 c1 : Bool) (p0 p1 p2 p3 : K) :
    let a := p0 + (c0.toNat : K) * (p1 - p0)
    let b := p2 + (c0.toNat : K) * (p3 - p2)
    a + (c1.toNat : K) * (b - a) =
      if c0 then (if c1 then p3 else p1) else (if c1 then p2 else p0) := by
  cases c0 <;> cases c1 <;> simp

/-- The `mux8` tree (bit 0 at the leaves, then bit 1, then bit 2) selects entry
`c0 + 2 c1 + 4 c2`. -/
theorem mux8_spec (c0 c1 c2 : Bool) (v : Fin 8 → K) :
    let m01 := v 0 + (c0.toNat : K) * (v 1 - v 0)
    let m23 := v 2 + (c0.toNat : K) * (v 3 - v 2)
    let m45 := v 4 + (c0.toNat : K) * (v 5 - v 4)
    let m67 := v 6 + (c0.toNat : K) * (v 7 - v 6)
    let m03 := m01 + (c1.toNat : K) * (m23 - m01)
    let m47 := m45 + (c1.toNat : K) * (m67 - m45)
    m03 + (c2.toNat : K) * (m47 - m03) =
      v ⟨c0.toNat + 2 * c1.toNat + 4 * c2.toNat, by
        cases c0 <;> cases c1 <;> cases c2 <;> decide⟩ := by
  cases c0 <;> cases c1 <;> cases c2 <;> simp

/-- The affine-addition rows of `affAdd`, given the guard `xq - xp ≠ 0`. -/
theorem affAdd_rows {xp yp xq yq l x y : K}
    (h₁ : (xq - xp) * l = yq - yp)
    (h₂ : l * l - xp - xq - x = 0)
    (h₃ : l * (xp - x) - yp - y = 0) :
    l * (xq - xp) = yq - yp ∧ l * l = xp + xq + x ∧ l * (xp - x) = yp + y := by
  refine ⟨by linear_combination h₁, by linear_combination h₂, by linear_combination h₃⟩

/-- The affine-doubling rows of `affDouble`. -/
theorem affDouble_rows {x y l x' y' : K}
    (h₁ : (2 * y) * l - (3 * x * x + (-3)) = 0)
    (h₂ : l * l - 2 * x - x' = 0)
    (h₃ : l * (x - x') - y - y' = 0) :
    (2 * y) * l = 3 * x ^ 2 + (-3) ∧ l * l = 2 * x + x' ∧ l * (x - x') = y + y' := by
  refine ⟨by linear_combination h₁, by linear_combination h₂, by linear_combination h₃⟩

/-- The five ELM rows of `elmCore` + `elm`, in the shape consumed by
`Math.ElmAlgebra.elm_two_additions`. -/
theorem elm_rows {xA yA xB yB xU xS yS l₁ l₂ : K}
    (h₁ : (xB - xA) * l₁ = yB - yA)
    (h₂ : l₁ * l₁ - xA - xB - xU = 0)
    (h₃ : (l₁ + l₂) * (xA - xU) - 2 * yA = 0)
    (h₄ : l₂ * l₂ - xA - xU - xS = 0)
    (h₅ : l₂ * (xA - xS) - yA - yS = 0) :
    l₁ * (xB - xA) = yB - yA ∧ l₁ * l₁ = xA + xB + xU ∧
      (l₁ + l₂) * (xA - xU) = 2 * yA ∧ l₂ * l₂ = xA + xU + xS ∧
      l₂ * (xA - xS) = yS + yA := by
  refine ⟨by linear_combination h₁, by linear_combination h₂,
    by linear_combination h₃, by linear_combination h₄, by linear_combination h₅⟩

end StandardECDSA.Gadgets
