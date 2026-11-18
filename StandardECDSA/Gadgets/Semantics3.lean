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
import StandardECDSA.Math.GroupOrder

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



/-! ## `affDouble` -/

def affDoubleMain (i : Var (fields 2) Fp) : Circuit Fp (Var (ProvablePair field field) Fp) :=
  affDouble (i[0], i[1])

instance : ElaboratedCircuit Fp (fields 2) (ProvablePair field field) affDoubleMain := by
  unfold affDoubleMain affDouble
  elaborate_circuit

theorem affDoubleMain_output (i : Var (fields 2) Fp) (n : ℕ) :
    ElaboratedCircuit.output affDoubleMain i n =
      (.var ⟨n + matLen (i[0].mul i[0]) + 1⟩, .var ⟨n + matLen (i[0].mul i[0]) + 2⟩) := by
  rw [← ElaboratedCircuit.output_eq]
  simp only [Circuit.output, affDoubleMain, affDouble, bind_fst, witnessField_fst,
    pure_fst, mm, mat_localLength_eq, witnessField_snd, assertZero_snd,
    Operations.localLength, Nat.add_zero]

def affDoubleEqs (i : fields 2 Fp) (out : Fp × Fp) : Prop :=
  ∃ l : Fp, (2 * i[1]) * l = 3 * (i[0] * i[0]) + pa ∧
    out.1 = l * l - 2 * i[0] ∧ out.2 = l * (i[0] - out.1) - i[1]

theorem affDoubleEqs_group (i : fields 2 Fp) (out : Fp × Fp)
    (hA : NS i[0] i[1]) (hy : 2 * i[1] ≠ 0) (h : affDoubleEqs i out) :
    ∃ hR : NS out.1 out.2,
      Affine.Point.some out.1 out.2 hR = 2 • Affine.Point.some i[0] i[1] hA := by
  obtain ⟨l, h1, h2, h3⟩ := h
  have hy' : i[1] ≠ Affine.negY Wp i[0] i[1] := by
    intro he
    apply hy
    dsimp [Affine.negY, Wp, StandardECDSA.Math.AffineBridge.W, CurveParameters.toMathlib] at he
    linear_combination he
  have hs : Affine.slope Wp i[0] i[0] i[1] i[1] = l := by
    rw [Affine.slope_of_Y_ne rfl hy']
    dsimp [Affine.negY, Wp, StandardECDSA.Math.AffineBridge.W, CurveParameters.toMathlib,
      StandardECDSA.params]
    simp only [mul_zero, zero_mul, sub_zero, sub_neg_eq_add, ← two_mul]
    rw [div_eq_iff (show (2 : Fp) * i[1] ≠ 0 from hy)]
    have hpa : pa = -3 := rfl
    rw [hpa] at h1
    linear_combination -h1
  have hX : Affine.addX Wp i[0] i[0] l = out.1 := by
    rw [h2]
    dsimp [Affine.addX, Wp, StandardECDSA.Math.AffineBridge.W, CurveParameters.toMathlib]
    ring
  have hY : Affine.addY Wp i[0] i[0] i[1] l = out.2 := by
    rw [h3]
    simp only [Affine.addY, Affine.negAddY, hX]
    dsimp [Affine.negY, Wp, StandardECDSA.Math.AffineBridge.W, CurveParameters.toMathlib]
    ring
  have hsum := Affine.Point.add_self_of_Y_ne (W := Wp) (h₁ := hA) hy'
  simp only [hs] at hsum
  obtain ⟨h', hsum'⟩ : ∃ h' : NS (Affine.addX Wp i[0] i[0] l) (Affine.addY Wp i[0] i[0] i[1] l),
      Affine.Point.some i[0] i[1] hA + Affine.Point.some i[0] i[1] hA
        = Affine.Point.some (Affine.addX Wp i[0] i[0] l) (Affine.addY Wp i[0] i[0] i[1] l) h' :=
    ⟨_, hsum⟩
  refine ⟨hX ▸ hY ▸ h', ?_⟩
  rw [two_nsmul, Affine.Point.add_self_of_Y_ne (h₁ := hA) hy', Affine.Point.some.injEq]
  exact ⟨by rw [hs]; exact hX.symm, by rw [hs]; exact hY.symm⟩

def affDoubleSpec (i : fields 2 Fp) (out : Fp × Fp) : Prop :=
  ∃ hA : NS i[0] i[1], ∃ hR : NS out.1 out.2,
    Affine.Point.some out.1 out.2 hR = 2 • Affine.Point.some i[0] i[1] hA

def affDoubleAssumptions (i : fields 2 Fp) : Prop :=
  NS i[0] i[1] ∧ 2 * i[1] ≠ 0

theorem affDoubleMain_soundness :
    Soundness Fp affDoubleMain affDoubleAssumptions affDoubleSpec := by
  circuit_proof_start
  obtain ⟨hA, hy⟩ := h_assumptions
  have hi0 : Expression.eval env input_var[0] = input[0] := by rw [← h_input]; simp
  have hi1 : Expression.eval env input_var[1] = input[1] := by rw [← h_input]; simp
  simp only [affDoubleMain, affDouble, circuit_norm, pm] at h_holds
  obtain ⟨r1, r2, r3, r4⟩ := h_holds
  have hxx' : Expression.eval env (mm input_var[0] input_var[0] i₀).1
      = input[0] * input[0] := by
    show Expression.eval env ((mat (.mul input_var[0] input_var[0])) i₀).1 = _
    rw [mat_output_eq]
    rw [mat_eval_gen (.mul input_var[0] input_var[0]) i₀ env
      { assert := fun e => Expression.eval env e = 0
        lookup := fun l => l.Soundness env
        interact := fun i => i.Guarantees env
        subcircuit := fun {m} s => s.Assumptions env → s.Spec env }
      (fun x hx => hx) r1]
    simp only [Expression.eval, hi0]
  have hlen : Operations.localLength (mm input_var[0] input_var[0] i₀).2
      = matLen (input_var[0].mul input_var[0]) := mat_localLength_eq _ i₀
  simp only [hlen] at r2 r3 r4
  simp only [hi0, hi1, cst, sc, Expression.eval] at r2 r3 r4
  rw [hxx'] at r2
  refine ⟨?_, ?_⟩
  · rw [affDoubleMain_output]
    simp only [Expression.eval]
    refine ⟨hA, affDoubleEqs_group input
      (env.get (i₀ + matLen (input_var[0].mul input_var[0]) + 1),
       env.get (i₀ + matLen (input_var[0].mul input_var[0]) + 2)) hA hy
      ⟨env.get (i₀ + matLen (input_var[0].mul input_var[0])), ?_, ?_, ?_⟩⟩
    · linear_combination r2
    · linear_combination -r3
    · linear_combination -r4
  · simp only [affDoubleMain, affDouble, mm, circuit_norm]
    exact mat_requirements (.mul input_var[0] input_var[0]) i₀ env

theorem affDoubleMain_completeness :
    Completeness Fp affDoubleMain affDoubleAssumptions := by
  circuit_proof_start
  obtain ⟨hA, hy⟩ := h_assumptions
  have hi0 : Expression.eval env input_var[0] = input[0] := by rw [← h_input]; simp
  have hi1 : Expression.eval env input_var[1] = input[1] := by rw [← h_input]; simp
  simp only [affDoubleMain, affDouble, mm, circuit_norm, pm] at h_env ⊢
  obtain ⟨e1, e2, e3, e4⟩ := h_env
  rw [mat_operations_eq] at e1
  have hlen : Operations.localLength (mat (input_var[0].mul input_var[0]) i₀).2
      = matLen (input_var[0].mul input_var[0]) := mat_localLength_eq _ i₀
  simp only [hlen] at e2 e3 e4 ⊢
  rw [Nat.add_comm (matLen (input_var[0].mul input_var[0])) i₀] at e2 e3 e4
  simp only [hi0, hi1, cst, sc, Expression.eval] at e2 e3 e4 ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mat_operations_eq]
    exact mat_complete _ i₀ env e1
  · have hy1 : input[1] ≠ 0 := by
      intro h; exact hy (by rw [h]; ring)
    have h2 : (2 : Fp) ≠ 0 := by decide
    rw [e2]
    field_simp
    ring
  · rw [e3]; ring
  · rw [e4]; ring

def affDoubleCircuit : FormalCircuit Fp (fields 2) (ProvablePair field field) where
  main := affDoubleMain
  Assumptions := affDoubleAssumptions
  Spec := affDoubleSpec
  soundness := affDoubleMain_soundness
  completeness := affDoubleMain_completeness
  requirementsChannelsLawful := by
    intro input offset
    simp only [affDoubleMain, affDouble, mm, circuit_norm]
    rw [mat_operations_eq]
    refine ⟨?_, ?_, ?_⟩
    · simpa using (matOps_requirementsChannelsLawful (input[0].mul input[0]) offset).1
    · intro channel hc
      have h := (matOps_requirementsChannelsLawful (input[0].mul input[0]) offset).2.1 channel hc
      simp only [List.not_mem_nil, false_or] at h
    · intro env hsh
      have h := (matOps_requirementsChannelsLawful (input[0].mul input[0]) offset).2.2 env hsh.1
      simpa [Operations.InChannelsOrRequirements] using h

/-! ## `elm` -/

def elmMain (i : Var (fields 4) Fp) : Circuit Fp (Var (ProvablePair field field) Fp) :=
  elm (i[0], i[1]) (i[2], i[3])

instance : ElaboratedCircuit Fp (fields 4) (ProvablePair field field) elmMain := by
  unfold elmMain elm elmCore nonzero
  elaborate_circuit

theorem elmMain_output (i : Var (fields 4) Fp) (n : ℕ) :
    ElaboratedCircuit.output elmMain i n = (.var ⟨n+4⟩, .var ⟨n+5⟩) := rfl

def elmEqs (i : fields 4 Fp) (out : Fp × Fp) : Prop :=
  ∃ (inv1 l1 xu l2 : Fp),
    (i[2] - i[0]) * inv1 = 1 ∧
    (i[2] - i[0]) * l1 = i[3] - i[1] ∧
    l1 * l1 - i[0] - i[2] - xu = 0 ∧
    (l1 + l2) * (i[0] - xu) - 2 * i[1] = 0 ∧
    l2 * l2 - i[0] - xu - out.1 = 0 ∧
    l2 * (i[0] - out.1) - i[1] - out.2 = 0

/-- A nonsingular affine point satisfies the short Weierstrass equation. -/
theorem ns_equation (x y : Fp) (h : NS x y) : y^2 = x^3 + params.a*x + params.b := by
  have hh := (Affine.equation_iff_nonsingular (W := Wp)).mpr h
  rw [Affine.equation_iff] at hh
  dsimp [Wp, StandardECDSA.Math.AffineBridge.W, CurveParameters.toMathlib] at hh
  linear_combination hh

theorem elmEqs_group (i : fields 4 Fp) (out : Fp × Fp)
    (hA : NS i[0] i[1]) (hB : NS i[2] i[3]) (h : elmEqs i out) :
    ∃ hR : NS out.1 out.2,
      Affine.Point.some out.1 out.2 hR
        = 2 • Affine.Point.some i[0] i[1] hA + Affine.Point.some i[2] i[3] hB := by
  obtain ⟨inv1, l1, xu, l2, hinv, h1, h2, h3, h4, h5⟩ := h
  have hDx : i[2] - i[0] ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hinv
    exact zero_ne_one hinv
  have hA' := ns_equation i[0] i[1] hA
  have hB' := ns_equation i[2] i[3] hB
  have hTwo : (2 : Fp) ≠ 0 := by decide
  have hDisc : 4*params.a^3+27*params.b^2 ≠ 0 := by decide
  have hres := StandardECDSA.Math.AffineBridge.elm_eq_group params i[0] i[1] i[2] i[3]
    xu out.1 out.2 l1 l2 hTwo hDisc hA' hB' hDx
    (by linear_combination h1) (by linear_combination h2) (by linear_combination h3)
    (by linear_combination h4) (by linear_combination h5)
  exact ⟨_, hres⟩

def elmSpec (i : fields 4 Fp) (out : Fp × Fp) : Prop :=
  ∃ hA : NS i[0] i[1], ∃ hB : NS i[2] i[3], ∃ hR : NS out.1 out.2,
    Affine.Point.some out.1 out.2 hR
      = 2 • Affine.Point.some i[0] i[1] hA + Affine.Point.some i[2] i[3] hB

/-- The `x`-coordinate of `P + Q` as computed by the first three ELM rows. -/
def elmXu (i : fields 4 Fp) : Fp :=
  let l1 := (i[3] - i[1]) * (i[2] - i[0])⁻¹
  l1 * l1 - i[0] - i[2]

def elmAssumptions (i : fields 4 Fp) : Prop :=
  NS i[0] i[1] ∧ NS i[2] i[3] ∧ i[2] - i[0] ≠ 0 ∧ i[0] - elmXu i ≠ 0

theorem elmMain_soundness :
    Soundness Fp elmMain elmAssumptions elmSpec := by
  circuit_proof_start
  obtain ⟨hA, hB, hDx, hD2⟩ := h_assumptions
  have hi0 : Expression.eval env input_var[0] = input[0] := by rw [← h_input]; simp
  have hi1 : Expression.eval env input_var[1] = input[1] := by rw [← h_input]; simp
  have hi2 : Expression.eval env input_var[2] = input[2] := by rw [← h_input]; simp
  have hi3 : Expression.eval env input_var[3] = input[3] := by rw [← h_input]; simp
  simp only [elmMain, elm, elmCore, nonzero, circuit_norm, pm] at h_holds
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := h_holds
  simp only [hi0, hi1, hi2, hi3, cst, sc, Expression.eval] at r1 r2 r3 r4 r5 r6
  refine ⟨?_, ?_⟩
  · rw [elmMain_output]
    simp only [Expression.eval]
    refine ⟨hA, hB, elmEqs_group input (env.get (i₀+4), env.get (i₀+5)) hA hB
      ⟨env.get i₀, env.get (i₀+1), env.get (i₀+2), env.get (i₀+3),
        ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · linear_combination r1
    · linear_combination r2
    · linear_combination r3
    · linear_combination r4
    · linear_combination r5
    · linear_combination r6
  · simp only [elmMain, elm, elmCore, nonzero, circuit_norm]

theorem elmMain_completeness :
    Completeness Fp elmMain elmAssumptions := by
  circuit_proof_start
  obtain ⟨hA, hB, hDx, hD2⟩ := h_assumptions
  have hi0 : Expression.eval env.toEnvironment input_var[0] = input[0] := by rw [← h_input]; simp
  have hi1 : Expression.eval env.toEnvironment input_var[1] = input[1] := by rw [← h_input]; simp
  have hi2 : Expression.eval env.toEnvironment input_var[2] = input[2] := by rw [← h_input]; simp
  have hi3 : Expression.eval env.toEnvironment input_var[3] = input[3] := by rw [← h_input]; simp
  simp only [elmMain, elm, elmCore, nonzero, circuit_norm, pm] at h_env ⊢
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h_env
  simp only [hi0, hi1, hi2, hi3, cst, sc, Expression.eval] at e1 e2 e3 e4 e5 e6 ⊢
  have hxu : input[0] - env.get (i₀ + 1 + 1) ≠ 0 := by
    have h : env.get (i₀ + 1 + 1) = elmXu input := by
      rw [e3, e2, e1]; simp only [elmXu]; ring_nf
    rw [h]; exact hD2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]; exact sub_eq_zero.mpr (mul_inv_cancel₀ hDx)
  · rw [e2, e1]; field_simp; ring
  · rw [e3]; ring
  · rw [e4]; field_simp; ring
  · rw [e5]; ring
  · rw [e6]; ring

def elmCircuit : FormalCircuit Fp (fields 4) (ProvablePair field field) where
  main := elmMain
  Assumptions := elmAssumptions
  Spec := elmSpec
  soundness := elmMain_soundness
  completeness := elmMain_completeness
  requirementsChannelsLawful := by
    intro input offset
    simp only [elmMain, elm, elmCore, nonzero, circuit_norm]

/-! ## `elmTo` -/

def elmToMain (i : Var (fields 6) Fp) : Circuit Fp (Var unit Fp) :=
  elmTo (i[0], i[1]) (i[2], i[3]) (i[4], i[5])

instance : ElaboratedCircuit Fp (fields 6) unit elmToMain := by
  unfold elmToMain elmTo elmCore nonzero
  elaborate_circuit

def elmToSpec (i : fields 6 Fp) : Prop :=
  ∃ hA : NS i[0] i[1], ∃ hB : NS i[2] i[3], ∃ hT : NS i[4] i[5],
    2 • Affine.Point.some i[0] i[1] hA + Affine.Point.some i[2] i[3] hB
      = Affine.Point.some i[4] i[5] hT

/-- First ELM slope, as computed from the inputs. -/
def elmToL1 (i : fields 6 Fp) : Fp := (i[3] - i[1]) * (i[2] - i[0])⁻¹
/-- `x`-coordinate of `P + Q`, as computed from the inputs. -/
def elmToXu (i : fields 6 Fp) : Fp := elmToL1 i * elmToL1 i - i[0] - i[2]
/-- Second ELM slope, as computed from the inputs. -/
def elmToL2 (i : fields 6 Fp) : Fp := 2 * i[1] * (i[0] - elmToXu i)⁻¹ - elmToL1 i

def elmToAssumptions (i : fields 6 Fp) : Prop :=
  NS i[0] i[1] ∧ NS i[2] i[3] ∧ NS i[4] i[5] ∧ i[2] - i[0] ≠ 0 ∧
    i[0] - elmToXu i ≠ 0 ∧
    i[4] = elmToL2 i * elmToL2 i - i[0] - elmToXu i ∧
    i[5] = elmToL2 i * (i[0] - i[4]) - i[1]

theorem elmToMain_soundness :
    FormalAssertion.Soundness Fp elmToMain elmToAssumptions elmToSpec := by
  circuit_proof_start
  obtain ⟨hA, hB, hT, hDx, hD2, hT4, hT5⟩ := h_assumptions
  have hi0 : Expression.eval env input_var[0] = input[0] := by rw [← h_input]; simp
  have hi1 : Expression.eval env input_var[1] = input[1] := by rw [← h_input]; simp
  have hi2 : Expression.eval env input_var[2] = input[2] := by rw [← h_input]; simp
  have hi3 : Expression.eval env input_var[3] = input[3] := by rw [← h_input]; simp
  have hi4 : Expression.eval env input_var[4] = input[4] := by rw [← h_input]; simp
  have hi5 : Expression.eval env input_var[5] = input[5] := by rw [← h_input]; simp
  simp only [elmToMain, elmTo, elmCore, nonzero, circuit_norm, pm] at h_holds
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := h_holds
  simp only [hi0, hi1, hi2, hi3, hi4, hi5, cst, sc, Expression.eval] at r1 r2 r3 r4 r5 r6
  refine ⟨?_, ?_⟩
  · have hA' := ns_equation input[0] input[1] hA
    have hB' := ns_equation input[2] input[3] hB
    have hTwo : (2 : Fp) ≠ 0 := by decide
    have hDisc : 4*params.a^3+27*params.b^2 ≠ 0 := by decide
    have hres := StandardECDSA.Math.AffineBridge.elm_eq_group params input[0] input[1]
      input[2] input[3] (env.get (i₀+2)) input[4] input[5]
      (env.get (i₀+1)) (env.get (i₀+3)) hTwo hDisc hA' hB' hDx
      (by linear_combination r2) (by linear_combination r3) (by linear_combination r4)
      (by linear_combination r5) (by linear_combination r6)
    refine ⟨hA, hB, hT, ?_⟩
    rw [← hres]
  · simp only [elmToMain, elmTo, elmCore, nonzero, circuit_norm]

theorem elmToMain_completeness :
    FormalAssertion.Completeness Fp elmToMain elmToAssumptions elmToSpec := by
  circuit_proof_start
  obtain ⟨hA, hB, hT, hDx, hD2, hT4, hT5⟩ := h_assumptions
  have hi0 : Expression.eval env.toEnvironment input_var[0] = input[0] := by rw [← h_input]; simp
  have hi1 : Expression.eval env.toEnvironment input_var[1] = input[1] := by rw [← h_input]; simp
  have hi2 : Expression.eval env.toEnvironment input_var[2] = input[2] := by rw [← h_input]; simp
  have hi3 : Expression.eval env.toEnvironment input_var[3] = input[3] := by rw [← h_input]; simp
  have hi4 : Expression.eval env.toEnvironment input_var[4] = input[4] := by rw [← h_input]; simp
  have hi5 : Expression.eval env.toEnvironment input_var[5] = input[5] := by rw [← h_input]; simp
  simp only [elmToMain, elmTo, elmCore, nonzero, circuit_norm, pm] at h_env ⊢
  obtain ⟨e1, e2, e3, e4⟩ := h_env
  simp only [hi0, hi1, hi2, hi3, hi4, hi5, cst, sc, Expression.eval] at e1 e2 e3 e4 ⊢
  have hxu : env.get (i₀ + 1 + 1) = elmToXu input := by
    rw [e3, e2, e1]; simp only [elmToXu, elmToL1]; ring_nf
  have hxu0 : input[0] - env.get (i₀ + 1 + 1) ≠ 0 := by
    rw [hxu]; exact hD2
  have hl1 : env.get (i₀ + 1) = elmToL1 input := by
    rw [e2, e1]; simp only [elmToL1]
  have hl2 : env.get (i₀ + 1 + 1 + 1) = elmToL2 input := by
    rw [e4, hxu, hl1]; simp only [elmToL2]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]; exact sub_eq_zero.mpr (mul_inv_cancel₀ hDx)
  · rw [e2, e1]; field_simp; ring
  · rw [e3]; ring
  · rw [e4]; field_simp; ring
  · rw [hl2, hxu]; linear_combination -hT4
  · rw [hl2]; linear_combination -hT5

def elmToAssertion : FormalAssertion Fp (fields 6) where
  main := elmToMain
  Assumptions := elmToAssumptions
  Spec := elmToSpec
  soundness := elmToMain_soundness
  completeness := elmToMain_completeness
  requirementsChannelsLawful := by
    intro input offset
    simp only [elmToMain, elmTo, elmCore, nonzero, circuit_norm]

end StandardECDSA.Gadgets
