/-
# `NoLookupSub`: the standard circuit has no lookups and no subcircuits

`ConstraintsHold.Completeness` and `ConstraintsHold.Soundness` differ only in
their `lookup` and `subcircuit` clauses.  For a circuit that never emits a
`Circuit.lookup` or a `Circuit.subcircuit` operation both clauses are vacuous,
so completeness implies soundness.  This file proves exactly that for the
standard P-256 ECDSA circuit `StandardECDSA.main`, discharging the `hl`/`hs`
hypotheses of `main_accepts_iff_standard` (gap G3 of `docs/m6-report.md`).

The development mirrors the `CostIs` API of `Challenge/Utils/CostR1CS.lean`:
`NoLookupSub` is a predicate on `Operations Fp`, preserved by `append`, by the
`Circuit` combinators (`pure`, `bind`, `map`, `witnessField`, `assertZero`,
`mapFinRange`, `foldlRange`) and by every gadget and phase of the circuit.

Lemma names carry an `nls_` prefix so that they do not shadow the gadget names
they are about (`mat`, `assertZeroLazy`, …), which would turn each theorem into
an accidental recursive definition.

Task T20 / gap G3.
-/
import StandardECDSA.Main

namespace StandardECDSA

open Circuit
open StandardECDSA.Gadgets
open StandardECDSA.Phases
open StandardECDSA.Math

/-! ## The predicate -/

/-- `ops` contains neither a `lookup` nor a `subcircuit` operation. -/
def NoLookupSub (ops : Operations Fp) : Prop :=
  ops.shallowLookups = [] ∧ ops.subcircuits = []

namespace NoLookupSub

/-! ## List-level structure -/

theorem nls_shallowLookups_append (a b : Operations Fp) :
    (a ++ b).shallowLookups = a.shallowLookups ++ b.shallowLookups := by
  induction a with
  | nil => rfl
  | cons op ops ih =>
      cases op <;> simp only [List.cons_append, Operations.shallowLookups, ih]

theorem nls_nil : NoLookupSub ([] : Operations Fp) := ⟨rfl, rfl⟩

theorem nls_append {a b : Operations Fp} (ha : NoLookupSub a) (hb : NoLookupSub b) :
    NoLookupSub (a ++ b) := by
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := hb
  refine ⟨?_, ?_⟩
  · rw [nls_shallowLookups_append, h1, h3, List.nil_append]
  · rw [Operations.subcircuits_append, h2, h4, List.nil_append]

theorem nls_witness (m : ℕ) (c : WitgenIR Fp m) :
    NoLookupSub [Operation.witness m c] := ⟨rfl, rfl⟩

theorem nls_assert (e : E) : NoLookupSub [Operation.assert e] := ⟨rfl, rfl⟩

theorem nls_flatten {l : List (Operations Fp)} (h : ∀ o ∈ l, NoLookupSub o) :
    NoLookupSub l.flatten := by
  induction l with
  | nil => exact nls_nil
  | cons a as ih =>
      rw [List.flatten_cons]
      exact nls_append (h a (by simp)) (ih (fun o ho => h o (by simp [ho])))

/-! ## `Circuit` combinators -/

variable {α β : Type}

theorem nls_pure (a : α) (n : ℕ) : NoLookupSub ((pure a : Circuit Fp α).operations n) := by
  rw [Circuit.pure_operations_eq]
  exact nls_nil

theorem nls_bind {f : Circuit Fp α} {g : α → Circuit Fp β} {n : ℕ}
    (hf : NoLookupSub (f.operations n))
    (hg : ∀ a, NoLookupSub ((g a).operations (n + f.localLength n))) :
    NoLookupSub ((f >>= g).operations n) := by
  rw [Circuit.bind_operations_eq]
  exact nls_append hf (hg _)

theorem nls_map {f : Circuit Fp α} {g : α → β} {n : ℕ} (hf : NoLookupSub (f.operations n)) :
    NoLookupSub ((g <$> f).operations n) := by
  rw [Circuit.map_operations_eq]
  exact hf

theorem nls_witnessField (e : Witgen.FExpr Fp) (n : ℕ) :
    NoLookupSub ((Circuit.witnessField e).operations n) := ⟨rfl, rfl⟩

theorem nls_assertZero (e : E) (n : ℕ) :
    NoLookupSub ((Circuit.assertZero e).operations n) := ⟨rfl, rfl⟩

theorem nls_mapFinRange {m : ℕ} [NeZero m] {body : Fin m → Circuit Fp β}
    {constant : Circuit.ConstantLength body} {n : ℕ}
    (h : ∀ i, NoLookupSub ((body i).operations (n + i * (body 0).localLength))) :
    NoLookupSub ((Circuit.mapFinRange m body constant).operations n) := by
  rw [Circuit.mapFinRange.operations_eq]
  refine nls_flatten (fun o ho => ?_)
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ho
  exact h i

theorem nls_foldlRange {m : ℕ} [Inhabited β] {init : β} {body : β → Fin m → Circuit Fp β}
    {constant : Circuit.ConstantLength fun (t : β × Fin m) => body t.1 t.2} {n : ℕ}
    (h : ∀ s i, NoLookupSub ((body s i).operations (n + i * (body default i).localLength))) :
    NoLookupSub ((Circuit.foldlRange m init body constant).operations n) := by
  rw [Circuit.foldlRange.operations_eq]
  refine nls_flatten (fun o ho => ?_)
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ho
  exact h _ i

/-! ## Field-level gadgets -/

theorem nls_matOps (e : E) (n : ℕ) : NoLookupSub (matOps e n) := by
  induction e generalizing n with
  | var v => exact nls_nil
  | const c => exact nls_nil
  | add a b iha ihb =>
      simp only [matOps]
      exact nls_append (iha n) (ihb _)
  | mul a b iha ihb =>
      simp only [matOps]
      refine nls_append (iha n) (nls_append (ihb _) ?_)
      split
      · exact nls_nil
      · exact nls_append (nls_witness _ _) (nls_assert _)

theorem nls_mat (e : E) (n : ℕ) : NoLookupSub ((mat e).operations n) := by
  rw [show (mat e).operations n = matOps e n from mat_operations_eq e n]
  exact nls_matOps e n

theorem nls_azlLoop (acc : E) (l : List (Fp × E)) (n : ℕ) :
    NoLookupSub ((azlLoop acc l).operations n) := by
  induction l generalizing acc n with
  | nil => exact nls_pure _ _
  | cons it rest ih =>
      simp only [azlLoop]
      exact nls_bind (nls_mat _ _) (fun w => ih _ _)

theorem nls_azlLinLoop (acc : E) (l : List (Fp × E)) (n : ℕ) :
    NoLookupSub ((azlLinLoop acc l).operations n) := by
  induction l generalizing acc n with
  | nil => exact nls_pure _ _
  | cons it rest ih =>
      simp only [azlLinLoop]
      exact ih _ _

theorem nls_assertZeroLazy (e : E) (n : ℕ) :
    NoLookupSub ((assertZeroLazy e).operations n) := by
  simp only [assertZeroLazy]
  cases h : (flat 1 e).filter (fun it => isProd it.2) with
  | nil =>
      simp only [h]
      exact nls_assertZero _ _
  | cons it rest =>
      obtain ⟨c, t⟩ := it
      cases t with
      | mul a b =>
          simp only [h]
          refine nls_bind (nls_mat a _) (fun a' => nls_bind (nls_mat b _) (fun b' => ?_))
          refine nls_bind (nls_azlLoop _ _ _) (fun acc => ?_)
          exact nls_bind (nls_azlLinLoop _ _ _) (fun acc => nls_assertZero _ _)
      | var v => simp only [h]; exact nls_pure _ _
      | const cc => simp only [h]; exact nls_pure _ _
      | add x y => simp only [h]; exact nls_pure _ _

theorem nls_isOnCurve (x y : E) (n : ℕ) : NoLookupSub ((isOnCurve x y).operations n) := by
  simp only [isOnCurve]
  exact nls_bind (nls_mat _ _) (fun xx => nls_assertZeroLazy _ _)

theorem nls_pointEquality (x y z px py : E) (n : ℕ) :
    NoLookupSub ((pointEquality x y z px py).operations n) := by
  simp only [pointEquality]
  refine nls_bind (nls_mat _ _) (fun z' => ?_)
  refine nls_bind (nls_assertZeroLazy _ _) (fun _ => ?_)
  exact nls_assertZeroLazy _ _

theorem nls_nonzero (x : E) (n : ℕ) : NoLookupSub ((nonzero x).operations n) := by
  simp only [nonzero]
  refine nls_bind (nls_witnessField _ _) (fun inv => ?_)
  exact nls_bind (nls_assertZero _ _) (fun _ => nls_pure _ _)

theorem nls_assertBool (b : E) (n : ℕ) : NoLookupSub ((Gadgets.assertBool b).operations n) := by
  simp only [Gadgets.assertBool]
  exact nls_assertZero _ _

theorem nls_sel (b x0 x1 : E) (n : ℕ) : NoLookupSub ((sel b x0 x1).operations n) := by
  simp only [sel]
  exact nls_mat _ _

theorem nls_selW (b x0 x1 : E) (n : ℕ) : NoLookupSub ((selW b x0 x1).operations n) := by
  simp only [selW]
  refine nls_bind (nls_witnessField _ _) (fun w => ?_)
  exact nls_bind (nls_assertZero _ _) (fun _ => nls_pure _ _)

theorem nls_muxConst4 (b0 b1 : E) (tab : Array (Fp × Fp)) (n : ℕ) :
    NoLookupSub ((muxConst4 b0 b1 tab).operations n) := by
  simp only [muxConst4]
  exact nls_bind (nls_mat _ _) (fun b01 => nls_pure _ _)

theorem nls_muxConst4W (b0 b1 : E) (tab : Array (Fp × Fp)) (n : ℕ) :
    NoLookupSub ((muxConst4W b0 b1 tab).operations n) := by
  simp only [muxConst4W]
  refine nls_bind (nls_witnessField _ _) (fun b01 => ?_)
  exact nls_bind (nls_assertZero _ _) (fun _ => nls_pure _ _)

theorem nls_mux4 (b0 b1 : E) (p0 p1 p2 p3 : Pt) (n : ℕ) :
    NoLookupSub ((mux4 b0 b1 p0 p1 p2 p3).operations n) := by
  simp only [mux4]
  refine nls_bind (nls_sel _ _ _ _) (fun ax => ?_)
  refine nls_bind (nls_sel _ _ _ _) (fun bx => ?_)
  refine nls_bind (nls_sel _ _ _ _) (fun x => ?_)
  refine nls_bind (nls_sel _ _ _ _) (fun ay => ?_)
  refine nls_bind (nls_sel _ _ _ _) (fun by' => ?_)
  exact nls_bind (nls_sel _ _ _ _) (fun y => nls_pure _ _)

theorem nls_mux4W (b0 b1 : E) (p0 p1 p2 p3 : Pt) (n : ℕ) :
    NoLookupSub ((mux4W b0 b1 p0 p1 p2 p3).operations n) := by
  simp only [mux4W]
  refine nls_bind (nls_selW _ _ _ _) (fun ax => ?_)
  refine nls_bind (nls_selW _ _ _ _) (fun bx => ?_)
  refine nls_bind (nls_selW _ _ _ _) (fun x => ?_)
  refine nls_bind (nls_selW _ _ _ _) (fun ay => ?_)
  refine nls_bind (nls_selW _ _ _ _) (fun by' => ?_)
  exact nls_bind (nls_selW _ _ _ _) (fun y => nls_pure _ _)

theorem nls_affAdd (p q : Pt) (n : ℕ) : NoLookupSub ((affAdd p q).operations n) := by
  simp only [affAdd]
  refine nls_bind (nls_nonzero _ _) (fun inv => ?_)
  refine nls_bind (nls_witnessField _ _) (fun l => ?_)
  refine nls_bind (nls_assertZero _ _) (fun _ => ?_)
  refine nls_bind (nls_witnessField _ _) (fun x => ?_)
  refine nls_bind (nls_assertZero _ _) (fun _ => ?_)
  refine nls_bind (nls_witnessField _ _) (fun y => ?_)
  exact nls_bind (nls_assertZero _ _) (fun _ => nls_pure _ _)

theorem nls_affDouble (p : Pt) (n : ℕ) : NoLookupSub ((affDouble p).operations n) := by
  simp only [affDouble]
  refine nls_bind (nls_mat _ _) (fun xx => ?_)
  refine nls_bind (nls_witnessField _ _) (fun l => ?_)
  refine nls_bind (nls_assertZero _ _) (fun _ => ?_)
  refine nls_bind (nls_witnessField _ _) (fun x => ?_)
  refine nls_bind (nls_assertZero _ _) (fun _ => ?_)
  refine nls_bind (nls_witnessField _ _) (fun y => ?_)
  exact nls_bind (nls_assertZero _ _) (fun _ => nls_pure _ _)

theorem nls_elmCore (p q : Pt) (n : ℕ) : NoLookupSub ((elmCore p q).operations n) := by
  simp only [elmCore]
  refine nls_bind (nls_nonzero _ _) (fun inv1 => ?_)
  refine nls_bind (nls_witnessField _ _) (fun l1 => ?_)
  refine nls_bind (nls_assertZero _ _) (fun _ => ?_)
  refine nls_bind (nls_witnessField _ _) (fun xu => ?_)
  refine nls_bind (nls_assertZero _ _) (fun _ => ?_)
  refine nls_bind (nls_witnessField _ _) (fun l2 => ?_)
  exact nls_bind (nls_assertZero _ _) (fun _ => nls_pure _ _)

theorem nls_elm (p q : Pt) (n : ℕ) : NoLookupSub ((elm p q).operations n) := by
  simp only [elm]
  refine nls_bind (nls_elmCore _ _ _) (fun xu_l2 => ?_)
  refine nls_bind (nls_witnessField _ _) (fun x => ?_)
  refine nls_bind (nls_assertZero _ _) (fun _ => ?_)
  refine nls_bind (nls_witnessField _ _) (fun y => ?_)
  exact nls_bind (nls_assertZero _ _) (fun _ => nls_pure _ _)

theorem nls_elmTo (p q target : Pt) (n : ℕ) :
    NoLookupSub ((elmTo p q target).operations n) := by
  simp only [elmTo]
  refine nls_bind (nls_elmCore _ _ _) (fun xu_l2 => ?_)
  refine nls_bind (nls_assertZero _ _) (fun _ => ?_)
  exact nls_assertZero _ _

theorem nls_ltLoop (a : Nat → E) (missing : E) (l : List (Nat × Nat × Bool)) (n : ℕ) :
    NoLookupSub ((ltLoop a missing l).operations n) := by
  induction l generalizing missing n with
  | nil => exact nls_pure _ _
  | cons it rest ih =>
      obtain ⟨hi, lo, bit⟩ := it
      cases bit with
      | true =>
          simp only [ltLoop, ↓reduceIte]
          exact ih _ _
      | false =>
          simp only [ltLoop, ↓reduceIte]
          exact nls_bind (nls_witnessField _ _)
            (fun q => nls_bind (nls_assertZero _ _) (fun _ => ih _ _))

theorem nls_ltLoopGuarded (a : Nat → E) (guard missing : E) (l : List (Nat × Nat × Bool))
    (n : ℕ) : NoLookupSub ((ltLoopGuarded a guard missing l).operations n) := by
  induction l generalizing missing n with
  | nil => exact nls_pure _ _
  | cons it rest ih =>
      obtain ⟨hi, lo, bit⟩ := it
      cases bit with
      | true =>
          simp only [ltLoopGuarded, ↓reduceIte]
          exact ih _ _
      | false =>
          simp only [ltLoopGuarded, ↓reduceIte]
          refine nls_bind (nls_witnessField _ _) (fun q => ?_)
          exact nls_bind (nls_assertZero _ _) (fun _ => ih _ _)

theorem nls_assertLtOrderOf (bound : Nat) (a : Nat → E) (n : ℕ) :
    NoLookupSub ((assertLtOrderOf bound a).operations n) := by
  simp only [assertLtOrderOf]
  exact nls_ltLoop _ _ _ _

theorem nls_assertLtOrderGuardedOf (bound : Nat) (guard : E) (a : Nat → E) (n : ℕ) :
    NoLookupSub ((assertLtOrderGuardedOf bound guard a).operations n) := by
  simp only [assertLtOrderGuardedOf]
  exact nls_ltLoopGuarded _ _ _ _ _

/-! ## Circuit phases -/

theorem nls_hint (i : Nat) (n : ℕ) : NoLookupSub ((hint i).operations n) := by
  simp only [hint]
  exact nls_witnessField _ _

theorem nls_bitBody (base stride : Nat) (i : Fin 256) (n : ℕ) :
    NoLookupSub ((bitBody base stride i).operations n) := by
  rw [bitBody_ops]
  exact nls_append (nls_hint _ _) (nls_assertBool _ _)

theorem nls_bitVec (base stride : Nat) (n : ℕ) :
    NoLookupSub ((bitVec base stride).operations n) := by
  simp only [bitVec]
  exact nls_mapFinRange (fun i => nls_bitBody _ _ _ _)

theorem nls_seedPhase (inp : Var Input Fp) (n : ℕ) :
    NoLookupSub ((seedPhase inp).operations n) := by
  simp only [seedPhase, Circuit.operations]
  exact nls_append (nls_append (nls_append (nls_append (nls_hint 0 n) (nls_hint 1 _))
    (nls_hint 2 _)) (nls_hint 3 _)) (nls_assertBool _ _)

theorem nls_curvePhase (inp : Var Input Fp) (s : Seed) (n : ℕ) :
    NoLookupSub ((curvePhase inp s).operations n) := by
  rw [curvePhase_ops]
  exact nls_append (nls_append (nls_isOnCurve _ _ _) (nls_isOnCurve _ _ _))
    (nls_isOnCurve _ _ _)

theorem nls_nonzeroPhase (inp : Var Input Fp) (n : ℕ) :
    NoLookupSub ((nonzeroPhase inp).operations n) := by
  rw [nonzeroPhase_ops]
  exact nls_append (nls_nonzero _ _) (nls_nonzero _ _)

theorem nls_bitsPhase (n : ℕ) : NoLookupSub ((bitsPhase).operations n) := by
  simp only [bitsPhase, Circuit.operations]
  exact nls_append (nls_append (nls_bitVec _ _ _) (nls_bitVec _ _ _)) (nls_bitVec _ _ _)

theorem nls_bindPhase (inp : Var Input Fp) (b : Bits) (n : ℕ) :
    NoLookupSub ((bindPhase inp b).operations n) := by
  simp only [bindPhase, Circuit.operations]
  exact nls_append (nls_append (nls_append (nls_assertZero _ _) (nls_assertZero _ _))
    (nls_assertZero _ _)) (nls_assertZero _ _)

theorem nls_cmpPhase (b : Bits) (overflow : E) (n : ℕ) :
    NoLookupSub ((cmpPhase b overflow).operations n) := by
  rw [cmpPhase_ops]
  exact nls_append (nls_append (nls_assertLtOrderOf _ _ _) (nls_assertLtOrderOf _ _ _))
    (nls_assertLtOrderGuardedOf _ _ _ _)

theorem nls_fixedBaseBody (eb : Vector E 256) (tables : Array (Array (Fp × Fp))) (ep : Pt)
    (i : Fin 128) (n : ℕ) :
    NoLookupSub ((fixedBaseBody eb tables ep i).operations n) := by
  simp only [fixedBaseBody]
  exact nls_bind (nls_muxConst4W _ _ _ _) (fun t => nls_affAdd _ _ _)

theorem nls_fixedBase (h : Pt) (eb : Vector E 256) (n : ℕ) :
    NoLookupSub ((fixedBase h eb).operations n) := by
  rw [fixedBase_ops]
  exact nls_append (nls_affAdd _ _ _)
    (nls_foldlRange (fun s i => nls_fixedBaseBody _ _ s i _))

theorem nls_shiftedTables (h q r : Pt) (n : ℕ) :
    NoLookupSub ((shiftedTables h q r).operations n) := by
  rw [← shiftedTables_snd h q r n]
  simp only [shiftedTables]
  refine nls_bind (nls_affDouble _ _) (fun hh => ?_)
  refine nls_bind (nls_affAdd _ _ _) (fun hhh => ?_)
  refine nls_bind (nls_affAdd _ _ _) (fun p1 => ?_)
  refine nls_bind (nls_affAdd _ _ _) (fun p2 => ?_)
  refine nls_bind (nls_affAdd _ _ _) (fun p3 => ?_)
  refine nls_bind (nls_affAdd _ _ _) (fun m1 => ?_)
  refine nls_bind (nls_affAdd _ _ _) (fun m2 => ?_)
  exact nls_bind (nls_affAdd _ _ _) (fun m3 => nls_pure _ _)

theorem nls_jointLadderBody (tables : Tables) (rb sb : Vector E 256) (acc : Pt)
    (j : Fin 255) (n : ℕ) :
    NoLookupSub ((jointLadderBody tables rb sb acc j).operations n) := by
  rw [jointLadderBody_ops]
  exact nls_append (nls_mux4W _ _ _ _ _ _ _) (nls_elm _ _ _)

theorem nls_jointLadderFinal (tables : Tables) (rb sb : Vector E 256) (acc target : Pt)
    (n : ℕ) : NoLookupSub ((jointLadderFinal tables rb sb acc target).operations n) := by
  simp only [jointLadderFinal, Circuit.operations]
  exact nls_append (nls_mux4W _ _ _ _ _ _ _) (nls_elmTo _ _ _ _)

theorem nls_jointLadder (acc0 : Pt) (tables : Tables) (rb sb : Vector E 256) (target : Pt)
    (n : ℕ) : NoLookupSub ((jointLadder acc0 tables rb sb target).operations n) := by
  rw [jointLadder_ops]
  exact nls_append (nls_foldlRange (fun s i => nls_jointLadderBody _ _ _ s i _))
    (nls_jointLadderFinal _ _ _ _ _ _)

/-! ## The whole circuit -/

theorem nls_main (inp : Var Input Fp) (n : ℕ) : NoLookupSub ((main inp).operations n) := by
  rw [main_ops']
  exact nls_append (nls_append (nls_append (nls_append (nls_append (nls_append (nls_append
    (nls_append (nls_seedPhase _ _) (nls_curvePhase _ _ _)) (nls_nonzeroPhase _ _))
    (nls_bitsPhase _)) (nls_bindPhase _ _ _)) (nls_cmpPhase _ _ _)) (nls_fixedBase _ _ _))
    (nls_shiftedTables _ _ _ _)) (nls_jointLadder _ _ _ _ _ _)

end NoLookupSub

/-- The standard circuit's operations contain no lookup. -/
theorem main_shallowLookups_nil (inp : Var Input Fp) (n : ℕ) :
    ((main inp).operations n).shallowLookups = [] :=
  (NoLookupSub.nls_main inp n).1

/-- The standard circuit's operations contain no subcircuit. -/
theorem main_subcircuits_nil (inp : Var Input Fp) (n : ℕ) :
    ((main inp).operations n).subcircuits = [] :=
  (NoLookupSub.nls_main inp n).2

/-- **Acceptance equivalence for the actual circuit `main`, hypothesis-free.**

For an honest witness environment, the circuit's constraints hold exactly when
the six inputs satisfy the standard P-256 ECDSA verification predicate.  The two
structural side conditions of `main_accepts_iff_standard_of_nil` are discharged
here by `main_shallowLookups_nil` and `main_subcircuits_nil`, so this statement
carries no hypothesis about the shape of `main`'s operation list. -/
theorem main_accepts_iff_standard (inp : Var Input Fp) (penv : ProverEnvironment Fp) (n : Nat)
    (hw : penv.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (h : CompleteWitness inp penv n) :
    ConstraintsHold.Soundness penv ((main inp).operations n) ↔
      standardVerify (Expression.eval penv inp.pkX) (Expression.eval penv inp.pkY)
        (Expression.eval penv inp.digestLo) (Expression.eval penv inp.digestHi)
        (Expression.eval penv inp.r) (Expression.eval penv inp.s) :=
  main_accepts_iff_standard_of_nil inp penv n hw h
    (main_shallowLookups_nil inp n) (main_subcircuits_nil inp n)

end StandardECDSA
