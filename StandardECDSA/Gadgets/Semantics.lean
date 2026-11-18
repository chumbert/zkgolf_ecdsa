/-
# Bundled semantic specs for the field-level gadgets

Each gadget is exposed as a Clean `FormalAssertion` / `FormalCircuit` whose
`Spec` is a *field-level semantic* statement (Booleanity, invertibility,
selection), not a list of rows.  Soundness is proved from an arbitrary
satisfying assignment; completeness from the honest witness generator.

Task T05 / T10 (semantic half).
-/

import StandardECDSA.Gadgets.R1CS
import StandardECDSA.Gadgets.Lemmas
import Clean.Circuit.Formal

namespace StandardECDSA.Gadgets

/-! ## `assertBool` -/

/-- `assertBool` as a named circuit. -/
def assertBoolMain (b : Var field Fp) : Circuit Fp Unit := assertBool b

instance : ElaboratedCircuit Fp field unit assertBoolMain := by
  unfold assertBoolMain assertBool
  elaborate_circuit

theorem assertBoolMain_soundness :
    FormalAssertion.Soundness Fp assertBoolMain (fun _ => True) (fun b => b = 0 ∨ b = 1) := by
  circuit_proof_start
  simp only [assertBoolMain, assertBool, circuit_norm] at h_holds ⊢
  rw [h_input] at h_holds
  exact (bool_iff' input).mp h_holds

theorem assertBoolMain_completeness :
    FormalAssertion.Completeness Fp assertBoolMain (fun _ => True) (fun b => b = 0 ∨ b = 1) := by
  circuit_proof_start
  simp only [assertBoolMain, assertBool, circuit_norm] at h_assumptions h_spec ⊢
  rw [h_input]
  exact (bool_iff' input).mpr h_spec

/-- `assertBool` bundled as a `FormalAssertion`: the input is Boolean. -/
def assertBoolAssertion : FormalAssertion Fp field where
  main := assertBoolMain
  Assumptions := fun _ => True
  Spec := fun b => b = 0 ∨ b = 1
  soundness := assertBoolMain_soundness
  completeness := assertBoolMain_completeness

/-! ## `nonzero` -/

/-- `nonzero` as a named circuit. -/
def nonzeroMain (x : Var field Fp) : Circuit Fp (Var field Fp) := nonzero x

instance : ElaboratedCircuit Fp field field nonzeroMain := by
  unfold nonzeroMain nonzero
  elaborate_circuit

/-- The semantic spec of `nonzero`: `x` is invertible and the output is its
inverse. -/
def nonzeroSpec (x inv : Fp) : Prop := x ≠ 0 ∧ x * inv = 1

theorem nonzeroMain_soundness :
    Soundness Fp nonzeroMain (fun x => x ≠ 0) nonzeroSpec := by
  circuit_proof_start
  simp only [nonzeroMain, nonzero, circuit_norm, Expression.eval, pm, cst] at h_holds ⊢
  have hout : Expression.eval env (ElaboratedCircuit.output nonzeroMain input_var i₀) =
      env.get i₀ := rfl
  rw [hout, h_input] at *
  refine ⟨?_, ?_⟩
  · intro hx
    rw [hx, zero_mul, zero_sub] at h_holds
    exact (neg_ne_zero.mpr one_ne_zero) h_holds
  · linear_combination h_holds

theorem nonzeroMain_completeness :
    Completeness Fp nonzeroMain (fun x => x ≠ 0) := by
  circuit_proof_start
  simp only [nonzeroMain, nonzero, circuit_norm, Expression.eval, pm, cst] at h_assumptions h_env ⊢
  rw [h_env, h_input]
  exact sub_eq_zero.mpr (mul_inv_cancel₀ h_assumptions)

/-- `nonzero` bundled as a `FormalCircuit`. -/
def nonzeroCircuit : FormalCircuit Fp field field where
  main := nonzeroMain
  Assumptions := fun x => x ≠ 0
  Spec := nonzeroSpec
  soundness := nonzeroMain_soundness
  completeness := nonzeroMain_completeness

end StandardECDSA.Gadgets
