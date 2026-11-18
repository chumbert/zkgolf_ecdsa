/-
# `ExplicitCircuit` for `assertZeroLazy`, `isOnCurve` and `pointEquality`

`assertZeroLazy e` inspects `flat 1 e`, which is opaque for a symbolic `e`.  The
`ExplicitCircuit` instance therefore keeps `operations n := (assertZeroLazy e n).2`
and discharges the two structural side conditions by

* a case split on the *value* of `(flat 1 e).filter isProd` (the same split the
  cost certificate uses), and
* structural induction over the residual product list for `azlLoop` and over the
  linear list for `azlLinLoop`.

Task T05 (framework half).
-/

import StandardECDSA.Gadgets.MatExplicit
import StandardECDSA.Gadgets.Field

namespace StandardECDSA.Gadgets

/-- `ChannelsLawful` is preserved by concatenation when both channel lists are empty. -/
theorem channelsLawful_append (ops ops' : Operations Fp)
    (h1 : ops.ChannelsLawful []) (h2 : ops'.ChannelsLawful []) :
    (ops ++ ops').ChannelsLawful [] := by
  simpa using Operations.channelsLawful_append_of_channelsLawful (F := Fp) h1 h2

/-! ## `azlLinLoop` allocates nothing -/

theorem azlLinLoop_snd (acc : E) (l : List (Fp × E)) :
    ∀ n, ((azlLinLoop acc l) n).2 = [] := by
  induction l generalizing acc with
  | nil => intro n; rfl
  | cons it rest ih =>
      intro n
      simp only [azlLinLoop]
      exact ih _ n

theorem azlLinLoop_subcircuitsConsistent (acc : E) (l : List (Fp × E)) :
    ∀ n, Operations.SubcircuitsConsistent n ((azlLinLoop acc l) n).2 := by
  intro n
  rw [azlLinLoop_snd]
  simp [Operations.SubcircuitsConsistent, Operations.forAll]

theorem azlLinLoop_channelsLawful (acc : E) (l : List (Fp × E)) :
    ∀ n, Operations.ChannelsLawful ((azlLinLoop acc l) n).2 [] := by
  intro n
  rw [azlLinLoop_snd]
  simp [Operations.ChannelsLawful, Operations.subcircuitChannelsWithGuarantees,
    Operations.InChannelsOrGuarantees, Operations.SubcircuitChannelsLawful,
    Operations.forAllNoOffset, Operations.subcircuits]

/-! ## `azlLoop` -/

theorem azlLoop_subcircuitsConsistent (acc : E) (l : List (Fp × E)) :
    ∀ n, Operations.SubcircuitsConsistent n ((azlLoop acc l) n).2 := by
  induction l generalizing acc with
  | nil =>
      intro n
      simp [azlLoop, pure_snd, Operations.SubcircuitsConsistent, Operations.forAll]
  | cons it rest ih =>
      intro n
      obtain ⟨c, t⟩ := it
      simp only [azlLoop, bind_snd]
      rw [Operations.SubcircuitsConsistent, Operations.forAll_append]
      refine ⟨?_, ?_⟩
      · exact mat_subcircuitsConsistent t n
      · rw [mat_localLength_eq t n, Nat.add_comm (matLen t) n]
        exact ih _ _

theorem azlLoop_channelsLawful (acc : E) (l : List (Fp × E)) :
    ∀ n, Operations.ChannelsLawful ((azlLoop acc l) n).2 [] := by
  induction l generalizing acc with
  | nil =>
      intro n
      simp [azlLoop, pure_snd, Operations.ChannelsLawful, Operations.subcircuitChannelsWithGuarantees,
        Operations.InChannelsOrGuarantees, Operations.SubcircuitChannelsLawful,
        Operations.forAllNoOffset, Operations.subcircuits]
  | cons it rest ih =>
      intro n
      obtain ⟨c, t⟩ := it
      simp only [azlLoop, bind_snd]
      exact channelsLawful_append _ _ (mat_channelsLawful t n) (ih _ _)

/-! ## `assertZeroLazy` -/

theorem azl_subcircuitsConsistent (e : E) :
    ∀ n, Operations.SubcircuitsConsistent n ((assertZeroLazy e) n).2 := by
  intro n
  cases h : (flat 1 e).filter (fun it => isProd it.2) with
  | nil =>
      simp only [assertZeroLazy, h, Operations.SubcircuitsConsistent, assertZero_snd,
        Operations.forAll]
      trivial
  | cons it rest =>
      obtain ⟨c, t⟩ := it
      cases t with
      | var v =>
          simp only [assertZeroLazy, h, Operations.SubcircuitsConsistent, pure_snd,
            Operations.forAll]
      | const c' =>
          simp only [assertZeroLazy, h, Operations.SubcircuitsConsistent, pure_snd,
            Operations.forAll]
      | add a b =>
          simp only [assertZeroLazy, h, Operations.SubcircuitsConsistent, pure_snd,
            Operations.forAll]
      | mul a b =>
          simp only [assertZeroLazy, h, bind_snd, mat_localLength_eq, azlLinLoop_snd,
            List.append_nil, Operations.SubcircuitsConsistent]
          rw [Operations.forAll_append]
          refine ⟨mat_subcircuitsConsistent a n, ?_⟩
          rw [Operations.forAll_append]
          refine ⟨?_, ?_⟩
          · rw [mat_localLength_eq a n, Nat.add_comm (matLen a) n]
            exact mat_subcircuitsConsistent b (n + matLen a)
          · rw [Operations.forAll_append]
            refine ⟨?_, ?_⟩
            · rw [mat_localLength_eq a n, mat_localLength_eq b (n + matLen a)]
              rw [show matLen b + (matLen a + n) = n + matLen a + matLen b from by omega]
              exact azlLoop_subcircuitsConsistent _ rest _
            · simp only [assertZero_snd, Operations.forAll]
              trivial

theorem azl_channelsLawful (e : E) :
    ∀ n, Operations.ChannelsLawful ((assertZeroLazy e) n).2 [] := by
  intro n
  cases h : (flat 1 e).filter (fun it => isProd it.2) with
  | nil =>
      simp only [assertZeroLazy, h, assertZero_snd]
      simp [Operations.ChannelsLawful, Operations.subcircuitChannelsWithGuarantees,
        Operations.InChannelsOrGuarantees, Operations.SubcircuitChannelsLawful,
        Operations.forAllNoOffset, Operations.subcircuits]
  | cons it rest =>
      obtain ⟨c, t⟩ := it
      cases t with
      | var v =>
          simp only [assertZeroLazy, h, pure_snd]
          simp [Operations.ChannelsLawful, Operations.subcircuitChannelsWithGuarantees,
            Operations.InChannelsOrGuarantees, Operations.SubcircuitChannelsLawful,
            Operations.forAllNoOffset, Operations.subcircuits]
      | const c' =>
          simp only [assertZeroLazy, h, pure_snd]
          simp [Operations.ChannelsLawful, Operations.subcircuitChannelsWithGuarantees,
            Operations.InChannelsOrGuarantees, Operations.SubcircuitChannelsLawful,
            Operations.forAllNoOffset, Operations.subcircuits]
      | add a b =>
          simp only [assertZeroLazy, h, pure_snd]
          simp [Operations.ChannelsLawful, Operations.subcircuitChannelsWithGuarantees,
            Operations.InChannelsOrGuarantees, Operations.SubcircuitChannelsLawful,
            Operations.forAllNoOffset, Operations.subcircuits]
      | mul a b =>
          simp only [assertZeroLazy, h, bind_snd, mat_localLength_eq, azlLinLoop_snd,
            List.append_nil, List.nil_append]
          refine channelsLawful_append _ _ (mat_channelsLawful a n) ?_
          refine channelsLawful_append _ _ (mat_channelsLawful b _) ?_
          refine channelsLawful_append _ _ (azlLoop_channelsLawful _ rest _) ?_
          simp only [assertZero_snd]
          simp [Operations.ChannelsLawful, Operations.subcircuitChannelsWithGuarantees,
            Operations.InChannelsOrGuarantees, Operations.SubcircuitChannelsLawful,
            Operations.forAllNoOffset, Operations.subcircuits]

/-! ## Offset-independent local length

`ExplicitCircuits.IsElaborated` requires the explicit `localLength` to be
independent of the offset.  `azlLen` is the offset-free mirror of the number of
wires `assertZeroLazy e` allocates. -/

/-- Number of wires allocated by `assertZeroLazy e`, computed from `e` alone. -/
def azlLen (e : E) : ℕ :=
  match (flat 1 e).filter (fun it => isProd it.2) with
  | [] => 0
  | (_, .mul a b) :: rest => matLen a + matLen b + (rest.map (fun it => matLen it.2)).sum
  | _ => 0

theorem azlLoop_localLength (acc : E) (l : List (Fp × E)) :
    ∀ n, Operations.localLength ((azlLoop acc l) n).2
      = (l.map (fun it => matLen it.2)).sum := by
  induction l generalizing acc with
  | nil =>
      intro n
      simp [azlLoop, pure_snd, Operations.localLength]
  | cons it rest ih =>
      intro n
      obtain ⟨c, t⟩ := it
      simp only [azlLoop, bind_snd, List.map_cons, List.sum_cons,
        Operations.append_localLength, mat_localLength_eq]
      rw [ih]

theorem azl_localLength_eq (e : E) :
    ∀ n, Operations.localLength ((assertZeroLazy e) n).2 = azlLen e := by
  intro n
  cases h : (flat 1 e).filter (fun it => isProd it.2) with
  | nil =>
      simp only [assertZeroLazy, h, assertZero_snd, Operations.localLength, azlLen]
  | cons it rest =>
      obtain ⟨c, t⟩ := it
      cases t with
      | var v => simp only [assertZeroLazy, h, pure_snd, Operations.localLength, azlLen]
      | const c' => simp only [assertZeroLazy, h, pure_snd, Operations.localLength, azlLen]
      | add a b => simp only [assertZeroLazy, h, pure_snd, Operations.localLength, azlLen]
      | mul a b =>
          simp only [assertZeroLazy, h, bind_snd, azlLinLoop_snd, List.append_nil,
            Operations.append_localLength, mat_localLength_eq, azlLoop_localLength,
            assertZero_snd, Operations.localLength, azlLen]
          omega

@[instance_reducible, explicit_circuit_constructor]
def azlExplicit (e : E) : ExplicitCircuit (assertZeroLazy e) where
  output := fun _ => ()
  localLength := fun _ => azlLen e
  localLength_eq := azl_localLength_eq e
  operations := fun n => (assertZeroLazy e n).2
  subcircuitsConsistent := azl_subcircuitsConsistent e
  channelsWithGuarantees := fun _ => []
  channelsLawful := azl_channelsLawful e

instance (e : E) : ExplicitCircuit (assertZeroLazy e) := azlExplicit e

end StandardECDSA.Gadgets
