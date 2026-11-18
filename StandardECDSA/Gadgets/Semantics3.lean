/-
# Bundled semantic specs for the affine and ELM gadgets

Each gadget is exposed as a Clean `FormalCircuit` whose `Spec` is a *group*
statement: the output is the affine point obtained by the corresponding group
operation, and it lies on the curve.  Soundness is proved from an arbitrary
satisfying assignment (the distinct-`x` guard is *derived* from the enforced
inverse row); completeness assumes the actual denominator nonzeroness and never
uses the third ELM equation to construct the inverse that makes it true.

Task T08 / T09 (semantic half).
-/

import StandardECDSA.Gadgets.Semantics2
import StandardECDSA.Spec
import StandardECDSA.Math.AffineBridge

namespace StandardECDSA.Gadgets

open WeierstrassCurve

/-- The P-256 curve, as a Mathlib Weierstrass curve. -/
abbrev Wp : WeierstrassCurve Fp := StandardECDSA.Math.AffineBridge.W params

/-- `cst` evaluates to its constant. -/
theorem eval_cst (env : Environment Fp) (c : Fp) : Expression.eval env (cst c) = c := rfl

/-- Affine nonsingularity of `(x, y)` on the P-256 curve. -/
abbrev NS (x y : Fp) : Prop := Affine.Nonsingular Wp x y

/-! ## `affAdd` -/

/-- `affAdd` with the two input points flattened into four field inputs. -/
def affAddMain (i : Var (fields 4) Fp) : Circuit Fp (Var (ProvablePair field field) Fp) :=
  affAdd (i[0], i[1]) (i[2], i[3])

instance : ElaboratedCircuit Fp (fields 4) (ProvablePair field field) affAddMain := by
  unfold affAddMain affAdd
  elaborate_circuit

theorem affAddMain_output (i : Var (fields 4) Fp) (n : ℕ) :
    ElaboratedCircuit.output affAddMain i n = (.var ⟨n+2⟩, .var ⟨n+3⟩) := rfl

/-- The affine-addition equations, as produced by the four rows of `affAdd`. -/
def affAddEqs (i : fields 4 Fp) (out : Fp × Fp) : Prop :=
  ∃ l : Fp, (i[2] - i[0]) * l = i[3] - i[1] ∧
    out.1 = l * l - i[0] - i[2] ∧ out.2 = l * (i[0] - out.1) - i[1]

/-- The affine-addition equations give the group sum.  The output's on-curve
proof is *derived*, not assumed: the sum of two on-curve points with distinct
`x` is again an affine on-curve point. -/
theorem affAddEqs_group (i : fields 4 Fp) (out : Fp × Fp)
    (hA : NS i[0] i[1]) (hB : NS i[2] i[3])
    (hDx : i[2] - i[0] ≠ 0) (h : affAddEqs i out) :
    ∃ hR : NS out.1 out.2,
      Affine.Point.some out.1 out.2 hR
        = Affine.Point.some i[0] i[1] hA + Affine.Point.some i[2] i[3] hB := by
  obtain ⟨l, h1, h2, h3⟩ := h
  have hx : i[0] ≠ i[2] := by intro he; exact hDx (by rw [he]; ring)
  have hs : Affine.slope Wp i[0] i[2] i[1] i[3] = l := by
    rw [Affine.slope_of_X_ne hx]
    exact (div_eq_iff (sub_ne_zero.mpr hx)).mpr (by linear_combination h1)
  have hX : Affine.addX Wp i[0] i[2] l = out.1 := by
    rw [h2]
    dsimp [Affine.addX, Wp, StandardECDSA.Math.AffineBridge.W, CurveParameters.toMathlib]
    ring
  have hY : Affine.addY Wp i[0] i[2] i[1] l = out.2 := by
    rw [h3]
    simp only [Affine.addY, Affine.negAddY, hX]
    dsimp [Affine.negY, Wp, StandardECDSA.Math.AffineBridge.W, CurveParameters.toMathlib]
    ring
  have hsum := Affine.Point.add_of_X_ne (W := Wp) (h₁ := hA) (h₂ := hB) hx
  simp only [hs] at hsum
  obtain ⟨h', hsum'⟩ : ∃ h' : NS (Affine.addX Wp i[0] i[2] l) (Affine.addY Wp i[0] i[2] i[1] l),
      Affine.Point.some i[0] i[1] hA + Affine.Point.some i[2] i[3] hB
        = Affine.Point.some (Affine.addX Wp i[0] i[2] l) (Affine.addY Wp i[0] i[2] i[1] l) h' :=
    ⟨_, hsum⟩
  refine ⟨hX ▸ hY ▸ h', ?_⟩
  rw [hsum', Affine.Point.some.injEq]
  exact ⟨hX.symm, hY.symm⟩

/-- Semantic spec of `affAdd`: the output is the group sum of the two inputs. -/
def affAddSpec (i : fields 4 Fp) (out : Fp × Fp) : Prop :=
  ∃ hA : NS i[0] i[1], ∃ hB : NS i[2] i[3],
  ∃ hR : NS out.1 out.2,
    Affine.Point.some out.1 out.2 hR
      = Affine.Point.some i[0] i[1] hA + Affine.Point.some i[2] i[3] hB

/-- Assumptions of `affAdd`: both inputs are affine on-curve points with
distinct `x`-coordinates. -/
def affAddAssumptions (i : fields 4 Fp) : Prop :=
  NS i[0] i[1] ∧ NS i[2] i[3] ∧ i[2] - i[0] ≠ 0

theorem affAddMain_soundness :
    Soundness Fp affAddMain affAddAssumptions affAddSpec := by
  circuit_proof_start
  obtain ⟨hA, hB, hDx⟩ := h_assumptions
  have hi0 : Expression.eval env input_var[0] = input[0] := by rw [← h_input]; simp
  have hi1 : Expression.eval env input_var[1] = input[1] := by rw [← h_input]; simp
  have hi2 : Expression.eval env input_var[2] = input[2] := by rw [← h_input]; simp
  have hi3 : Expression.eval env input_var[3] = input[3] := by rw [← h_input]; simp
  simp only [affAddMain, affAdd, nonzero, circuit_norm, pm] at h_holds
  obtain ⟨r1, r2, r3, r4⟩ := h_holds
  simp only [hi0, hi1, hi2, hi3, cst, Expression.eval] at r1 r2 r3 r4
  refine ⟨?_, ?_⟩
  · rw [affAddMain_output]
    simp only [Expression.eval]
    refine ⟨hA, hB, affAddEqs_group input (env.get (i₀ + 2), env.get (i₀ + 3)) hA hB hDx
      ⟨env.get (i₀ + 1), ?_, ?_, ?_⟩⟩
    · linear_combination r2
    · show env.get (i₀ + 1 + 1) = env.get (i₀ + 1) * env.get (i₀ + 1) - input[0] - input[2]
      linear_combination -r3
    · show env.get (i₀ + 1 + 1 + 1) =
        env.get (i₀ + 1) * (input[0] - env.get (i₀ + 1 + 1)) - input[1]
      linear_combination -r4
  · simp only [affAddMain, affAdd, nonzero, circuit_norm]

theorem affAddMain_completeness :
    Completeness Fp affAddMain affAddAssumptions := by
  circuit_proof_start
  obtain ⟨hA, hB, hDx⟩ := h_assumptions
  have hi0 : Expression.eval env input_var[0] = input[0] := by rw [← h_input]; simp
  have hi1 : Expression.eval env input_var[1] = input[1] := by rw [← h_input]; simp
  have hi2 : Expression.eval env input_var[2] = input[2] := by rw [← h_input]; simp
  have hi3 : Expression.eval env input_var[3] = input[3] := by rw [← h_input]; simp
  have hDx' : Expression.eval env input_var[2] - Expression.eval env input_var[0] ≠ 0 := by
    rw [hi2, hi0]; exact hDx
  simp only [affAddMain, affAdd, nonzero, circuit_norm, pm] at h_env ⊢
  obtain ⟨e1, e2, e3, e4⟩ := h_env
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1]; simp only [eval_cst]; linear_combination mul_inv_cancel₀ hDx'
  · rw [e2, e1]; field_simp; ring
  · rw [e3]; ring
  · rw [e4]; ring

def affAddCircuit : FormalCircuit Fp (fields 4) (ProvablePair field field) where
  main := affAddMain
  Assumptions := affAddAssumptions
  Spec := affAddSpec
  soundness := affAddMain_soundness
  completeness := affAddMain_completeness
  requirementsChannelsLawful := by
    intro input offset
    simp only [affAddMain, affAdd, nonzero, circuit_norm]

end StandardECDSA.Gadgets
