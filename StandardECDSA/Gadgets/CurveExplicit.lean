/-
# `ExplicitCircuit` for `isOnCurve` and `pointEquality`

Both gadgets allocate a product wire and then feed it to `assertZeroLazy`.  The
number of wires `assertZeroLazy` allocates is a function of the *shape* of its
argument, and the argument mentions the freshly allocated wire, whose index
depends on the offset.  `VarShape.azlLen_eq` shows that the count is nevertheless
offset-independent, which is what Clean's `ExplicitCircuits.IsElaborated` side
condition needs.

Task T05 (framework half).
-/

import StandardECDSA.Gadgets.VarShape

namespace StandardECDSA.Gadgets

/-! ## `isOnCurve` -/

theorem isOnCurveExpr_varEq (x y : E) (n m : ℕ) :
    VarEq (Expression.mul y y - (Expression.mul x (matOut (Expression.mul x x) n) + sc pa x + cst pb))
          (Expression.mul y y - (Expression.mul x (matOut (Expression.mul x x) m) + sc pa x + cst pb)) :=
  .add (.mul (.refl y) (.refl y))
    (.mul (.const (-1))
      (.add (.add (.mul (.refl x) (matOut_varEq (.mul x x) n m))
                  (.mul (.const pa) (.refl x)))
            (.const pb)))

def isOnCurveExplicit (x y : E) : ExplicitCircuit (isOnCurve x y) where
  output := fun _ => ()
  localLength := fun _ =>
    matLen (.mul x x) + azlLen (Expression.mul y y - (Expression.mul x (matOut (Expression.mul x x) 0) + sc pa x + cst pb))
  localLength_eq := by
    intro n
    show Operations.localLength ((isOnCurve x y) n).2 = _
    simp only [isOnCurve, mm, bind_snd, Operations.append_localLength, mat_localLength_eq,
      mat_output_eq, azl_localLength_eq]
    rw [azlLen_eq (isOnCurveExpr_varEq x y n 0)]
  operations := fun n => (isOnCurve x y n).2
  subcircuitsConsistent :=
    (ExplicitCircuit.from_bind (matExplicit (.mul x x)) (fun _ => azlExplicit _)).subcircuitsConsistent
  channelsWithGuarantees := fun _ => []
  channelsLawful :=
    (ExplicitCircuit.from_bind (matExplicit (.mul x x)) (fun _ => azlExplicit _)).channelsLawful

/-! ## `pointEquality` -/

theorem pointEqualityExpr₁_varEq (x z px : E) (n m : ℕ) :
    VarEq (x - .mul (matOut z n) px) (x - .mul (matOut z m) px) :=
  .add (.refl x) (.mul (.const (-1)) (.mul (matOut_varEq z n m) (.refl px)))

theorem pointEqualityExpr₂_varEq (y z py : E) (n m : ℕ) :
    VarEq (y - .mul (matOut z n) py) (y - .mul (matOut z m) py) :=
  .add (.refl y) (.mul (.const (-1)) (.mul (matOut_varEq z n m) (.refl py)))

def pointEqualityExplicit (x y z px py : E) : ExplicitCircuit (pointEquality x y z px py) where
  output := fun _ => ()
  localLength := fun _ =>
    matLen z + azlLen (x - .mul (matOut z 0) px) + azlLen (y - .mul (matOut z 0) py)
  localLength_eq := by
    intro n
    show Operations.localLength ((pointEquality x y z px py) n).2 = _
    simp only [pointEquality, bind_snd, Operations.append_localLength, mat_localLength_eq,
      mat_output_eq, azl_localLength_eq]
    rw [azlLen_eq (pointEqualityExpr₁_varEq x z px n 0),
      azlLen_eq (pointEqualityExpr₂_varEq y z py n 0)]
    omega
  operations := fun n => (pointEquality x y z px py n).2
  subcircuitsConsistent :=
    (ExplicitCircuit.from_bind (matExplicit z)
      (fun _ => ExplicitCircuit.from_bind (azlExplicit _) (fun _ => azlExplicit _))).subcircuitsConsistent
  channelsWithGuarantees := fun _ => []
  channelsLawful :=
    (ExplicitCircuit.from_bind (matExplicit z)
      (fun _ => ExplicitCircuit.from_bind (azlExplicit _) (fun _ => azlExplicit _))).channelsLawful

/-! ## `ElaboratedCircuit` instances -/

def isOnCurveMain (i : Var (fields 2) Fp) : Circuit Fp (Var unit Fp) :=
  isOnCurve i[0] i[1]

def isOnCurveFamily : ExplicitCircuits (fun i : Var (fields 2) Fp => isOnCurve i[0] i[1]) :=
  ExplicitCircuits.fromSingle (fun i => isOnCurveExplicit i[0] i[1])

instance : ExplicitCircuits.IsElaborated
    (fun i : Var (fields 2) Fp => isOnCurve i[0] i[1]) isOnCurveFamily where
  localLength_eq := by intros; rfl
  channelsWithGuarantees_eq := by intros; rfl

instance : ElaboratedCircuit Fp (fields 2) unit isOnCurveMain :=
  ElaboratedCircuit.fromExplicit isOnCurveFamily
    (inferInstance : ExplicitCircuits.IsElaborated
      (fun i : Var (fields 2) Fp => isOnCurve i[0] i[1]) isOnCurveFamily)

def pointEqualityMain (i : Var (fields 5) Fp) : Circuit Fp (Var unit Fp) :=
  pointEquality i[0] i[1] i[2] i[3] i[4]

def pointEqualityFamily :
    ExplicitCircuits (fun i : Var (fields 5) Fp => pointEquality i[0] i[1] i[2] i[3] i[4]) :=
  ExplicitCircuits.fromSingle (fun i => pointEqualityExplicit i[0] i[1] i[2] i[3] i[4])

instance : ExplicitCircuits.IsElaborated
    (fun i : Var (fields 5) Fp => pointEquality i[0] i[1] i[2] i[3] i[4]) pointEqualityFamily where
  localLength_eq := by intros; rfl
  channelsWithGuarantees_eq := by intros; rfl

instance : ElaboratedCircuit Fp (fields 5) unit pointEqualityMain :=
  ElaboratedCircuit.fromExplicit pointEqualityFamily
    (inferInstance : ExplicitCircuits.IsElaborated
      (fun i : Var (fields 5) Fp => pointEquality i[0] i[1] i[2] i[3] i[4]) pointEqualityFamily)

end StandardECDSA.Gadgets
