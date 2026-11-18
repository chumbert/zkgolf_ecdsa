import StandardECDSA.Gadgets.AzlExplicit

namespace StandardECDSA.Gadgets

/-- Two expressions with the same shape, i.e. equal up to variable indices. -/
inductive VarEq : E → E → Prop where
  | var (i j : ℕ) : VarEq (.var ⟨i⟩) (.var ⟨j⟩)
  | const (c : Fp) : VarEq (.const c) (.const c)
  | add {a a' b b' : E} : VarEq a a' → VarEq b b' → VarEq (.add a b) (.add a' b')
  | mul {a a' b b' : E} : VarEq a a' → VarEq b b' → VarEq (.mul a b) (.mul a' b')

namespace VarEq

theorem refl (e : E) : VarEq e e := by
  induction e with
  | var v => cases v with | mk i => exact .var i i
  | const c => exact .const c
  | add a b iha ihb => exact .add iha ihb
  | mul a b iha ihb => exact .mul iha ihb

theorem deg_eq {e e' : E} (h : VarEq e e') : deg e = deg e' := by
  induction h with
  | var i j => rfl
  | const c => rfl
  | add _ _ iha ihb =>
      simp only [deg, Challenge.CostR1CS.degree] at iha ihb ⊢
      rw [iha, ihb]
  | mul _ _ iha ihb =>
      simp only [deg, Challenge.CostR1CS.degree] at iha ihb ⊢
      rw [iha, ihb]

theorem matLen_eq {e e' : E} (h : VarEq e e') : matLen e = matLen e' := by
  induction h with
  | var i j => rfl
  | const c => rfl
  | add _ _ iha ihb => simp only [matLen, iha, ihb]
  | mul ha hb iha ihb =>
      simp only [matLen, iha, ihb, deg_eq ha, deg_eq hb]

theorem constVal_eq {e e' : E} (h : VarEq e e') : constVal e = constVal e' := by
  induction h with
  | var i j => rfl
  | const c => rfl
  | add _ _ iha ihb =>
      simp only [constVal, Expression.eval] at iha ihb ⊢
      rw [iha, ihb]
  | mul _ _ iha ihb =>
      simp only [constVal, Expression.eval] at iha ihb ⊢
      rw [iha, ihb]

theorem isProd_eq {e e' : E} (h : VarEq e e') : isProd e = isProd e' := by
  induction h with
  | var i j => rfl
  | const c => rfl
  | add _ _ _ _ => rfl
  | mul _ _ _ _ => rfl

theorem forall₂_append {l₁ l₁' l₂ l₂' : List (Fp × E)}
    (h₁ : List.Forall₂ (fun it it' => it.1 = it'.1 ∧ VarEq it.2 it'.2) l₁ l₁')
    (h₂ : List.Forall₂ (fun it it' => it.1 = it'.1 ∧ VarEq it.2 it'.2) l₂ l₂') :
    List.Forall₂ (fun it it' => it.1 = it'.1 ∧ VarEq it.2 it'.2) (l₁ ++ l₂) (l₁' ++ l₂') := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h ih

theorem flat_eq {e e' : E} (h : VarEq e e') (c : Fp) :
    List.Forall₂ (fun it it' => it.1 = it'.1 ∧ VarEq it.2 it'.2) (flat c e) (flat c e') := by
  induction h generalizing c with
  | var i j => exact .cons ⟨rfl, .var i j⟩ .nil
  | const c' => exact .cons ⟨rfl, .const c'⟩ .nil
  | add ha hb iha ihb =>
      simp only [flat]
      exact forall₂_append (iha c) (ihb c)
  | mul ha hb iha ihb =>
      simp only [flat, deg_eq ha, deg_eq hb, constVal_eq ha, constVal_eq hb]
      split
      · exact ihb _
      · split
        · exact iha _
        · exact .cons ⟨rfl, .mul ha hb⟩ .nil

end VarEq

/-! ## `azlLen` is invariant -/

theorem sum_map_matLen_eq {l l' : List (Fp × E)}
    (h : List.Forall₂ (fun it it' => it.1 = it'.1 ∧ VarEq it.2 it'.2) l l') :
    (l.map (fun it => matLen it.2)).sum = (l'.map (fun it => matLen it.2)).sum := by
  induction h with
  | nil => rfl
  | cons hd _ ih =>
      obtain ⟨_, hv⟩ := hd
      simp only [List.map_cons, List.sum_cons, VarEq.matLen_eq hv, ih]

theorem forall₂_filter {l l' : List (Fp × E)}
    (h : List.Forall₂ (fun it it' => it.1 = it'.1 ∧ VarEq it.2 it'.2) l l') :
    List.Forall₂ (fun it it' => it.1 = it'.1 ∧ VarEq it.2 it'.2)
      (l.filter (fun it => isProd it.2)) (l'.filter (fun it => isProd it.2)) := by
  induction h with
  | nil => exact .nil
  | cons hd _ ih =>
      obtain ⟨hc, hv⟩ := hd
      simp only [List.filter_cons, VarEq.isProd_eq hv]
      split
      · exact .cons ⟨hc, hv⟩ ih
      · exact ih

/-- `azlLen` on an already-filtered item list. -/
def azlLenList (l : List (Fp × E)) : ℕ :=
  match l with
  | [] => 0
  | (_, .mul a b) :: rest => matLen a + matLen b + (rest.map (fun it => matLen it.2)).sum
  | _ => 0

theorem azlLen_eq_azlLenList (e : E) :
    azlLen e = azlLenList ((flat 1 e).filter (fun it => isProd it.2)) := rfl

theorem azlLenList_eq {l l' : List (Fp × E)}
    (h : List.Forall₂ (fun it it' => it.1 = it'.1 ∧ VarEq it.2 it'.2) l l') :
    azlLenList l = azlLenList l' := by
  match l, l', h with
  | [], [], _ => rfl
  | (c, t) :: rest, (c', t') :: rest', .cons hd tl =>
      obtain ⟨hc, hv⟩ := hd
      cases hv with
      | var i j => rfl
      | const c'' => rfl
      | add _ _ => rfl
      | mul ha hb =>
          simp only [azlLenList, VarEq.matLen_eq ha, VarEq.matLen_eq hb, sum_map_matLen_eq tl]

theorem azlLen_eq {e e' : E} (h : VarEq e e') : azlLen e = azlLen e' := by
  rw [azlLen_eq_azlLenList, azlLen_eq_azlLenList]
  exact azlLenList_eq (forall₂_filter (VarEq.flat_eq h 1))

/-! ## `matOut` is shape-invariant -/

theorem matOut_varEq (e : E) : ∀ n m, VarEq (matOut e n) (matOut e m) := by
  induction e with
  | var v => intro n m; exact .var _ _
  | const c => intro n m; exact .const c
  | add a b iha ihb =>
      intro n m
      simp only [matOut]
      exact .add (iha n m) (ihb _ _)
  | mul a b iha ihb =>
      intro n m
      simp only [matOut]
      split
      · exact .mul (iha n m) (ihb _ _)
      · exact .var _ _

end StandardECDSA.Gadgets
