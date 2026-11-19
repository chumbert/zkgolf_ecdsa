/-
# Witness-generator causality for the standard circuit

The plan's item 5 asks for a *truthful* causality statement for the honest witness
generator: generator evaluation must agree between environments that agree on the
earlier wires **and on the relevant hint provider**.  This is the hint-aware
strengthening of Clean's `Circuit.ComputableWitnesses`, whose `AgreesBelow`
hypothesis constrains only `ProverEnvironment.get` and is therefore unsatisfiable
for a `FExpr.hintGet` leaf (see `StandardECDSA/HintCausality.lean` and
`StandardECDSA/Interface.lean`).

This file supplies

* `EnvAgree n env env'` — wires below `n`, the hint provider and the prover data
  all agree;
* the syntactic predicates `Below` / `FBelow` / `U64Below` / `BBelow` recording
  that an expression only reads cells below the current offset, together with
  their semantic agreement lemmas;
* the operation certificate `OpsCausal`, preserved by `append` and by every
  `Circuit` combinator, and proved for every gadget and phase of the circuit;
* `main_causal`, the whole-circuit causality theorem;
* `main_ulwc_exists`, the concrete `ProverEnvironment` built by
  `Circuit.proverEnvironment`, which supplies the local witnesses of `main`.

Task T18 (fixed-hint causality) and gap G2 of `docs/m6-report.md`.
-/
import StandardECDSA.Main

namespace StandardECDSA

open Circuit
open StandardECDSA.Gadgets
open StandardECDSA.Phases
open StandardECDSA.Math

/-! ## Environment agreement -/

/-- Two prover environments agree below `n` when they have the same wires below
`n`, the same hint provider and the same prover data. -/
def EnvAgree (n : ℕ) (env env' : ProverEnvironment Fp) : Prop :=
  (∀ i < n, env.get i = env'.get i) ∧ env.hint = env'.hint ∧ env.data = env'.data

theorem EnvAgree.refl (n : ℕ) (env : ProverEnvironment Fp) : EnvAgree n env env :=
  ⟨fun _ _ => rfl, rfl, rfl⟩

theorem EnvAgree.mono {n m : ℕ} {env env' : ProverEnvironment Fp}
    (h : EnvAgree m env env') (hnm : n ≤ m) : EnvAgree n env env' :=
  ⟨fun i hi => h.1 i (Nat.lt_of_lt_of_le hi hnm), h.2⟩

theorem EnvAgree.symm {n : ℕ} {env env' : ProverEnvironment Fp}
    (h : EnvAgree n env env') : EnvAgree n env' env :=
  ⟨fun i hi => (h.1 i hi).symm, h.2.1.symm, h.2.2.symm⟩

theorem EnvAgree.trans {n : ℕ} {env env' env'' : ProverEnvironment Fp}
    (h : EnvAgree n env env') (h' : EnvAgree n env' env'') : EnvAgree n env env'' :=
  ⟨fun i hi => (h.1 i hi).trans (h'.1 i hi), h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩

/-! ## Expressions reading below an offset -/

/-- `e` only reads environment cells below `m`.  This is a *syntactic* predicate,
so that it can be decomposed along the expression tree. -/
def Below (m : ℕ) : E → Prop
  | .var v => v.index < m
  | .const _ => True
  | .add a b => Below m a ∧ Below m b
  | .mul a b => Below m a ∧ Below m b

namespace Below

theorem mono {n m : ℕ} {e : E} (h : Below n e) (hnm : n ≤ m) : Below m e := by
  induction e with
  | var v => exact Nat.lt_of_lt_of_le h hnm
  | const c => trivial
  | add a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | mul a b iha ihb => exact ⟨iha h.1, ihb h.2⟩

theorem var {m i : ℕ} (h : i < m) : Below m (Expression.var (F := Fp) ⟨i⟩) := h

theorem const (m : ℕ) (c : Fp) : Below m (Expression.const c) := trivial

theorem add {m : ℕ} {a b : E} (ha : Below m a) (hb : Below m b) : Below m (a + b) :=
  ⟨ha, hb⟩

theorem mul {m : ℕ} {a b : E} (ha : Below m a) (hb : Below m b) : Below m (a * b) :=
  ⟨ha, hb⟩

theorem neg {m : ℕ} {a : E} (ha : Below m a) : Below m (-a) := ⟨trivial, ha⟩

theorem sub {m : ℕ} {a b : E} (ha : Below m a) (hb : Below m b) : Below m (a - b) :=
  ⟨ha, ⟨trivial, hb⟩⟩

theorem sc {m : ℕ} (c : Fp) {a : E} (ha : Below m a) : Below m (sc c a) :=
  ⟨trivial, ha⟩

theorem cst (m : ℕ) (c : Fp) : Below m (cst c) := trivial

/-- Semantic content: an expression reading below `m` evaluates identically in
two environments that agree below `m`. -/
theorem eval_agree {m : ℕ} {e : E} (h : Below m e) :
    ∀ env env' : Environment Fp, (∀ i < m, env.get i = env'.get i) →
      Expression.eval env e = Expression.eval env' e := by
  induction e with
  | var v => intro env env' hag; exact hag v.index h
  | const c => intro env env' _; rfl
  | add a b iha ihb =>
      intro env env' hag
      show Expression.eval env a + Expression.eval env b =
        Expression.eval env' a + Expression.eval env' b
      rw [iha h.1 env env' hag, ihb h.2 env env' hag]
  | mul a b iha ihb =>
      intro env env' hag
      show Expression.eval env a * Expression.eval env b =
        Expression.eval env' a * Expression.eval env' b
      rw [iha h.1 env env' hag, ihb h.2 env env' hag]

end Below

/-! ## Witness-IR expressions reading below an offset

The witness-IR expression types are *mutually* inductive, so `induction` cannot be
used on them.  Following the pattern of `Baseline/ECDSA_P256_Digest/CompWit.lean`
we therefore state the three predicates *semantically* (as agreement of the
evaluated generator) and prove one constructor lemma per syntactic form.  The
circuit only ever builds generators from `.expr`, `.const`, `.add`, `.mul`,
`.inv`, `.ite` and `.hintGet`, so this covers every site. -/

/-- A field-sorted witness-IR expression whose evaluation only depends on the
environment below `m`. -/
def FBelow (m : ℕ) (f : Witgen.FExpr Fp) : Prop :=
  ∀ env env' : ProverEnvironment Fp, EnvAgree m env env' →
    Witgen.FExpr.eval { env := env } f = Witgen.FExpr.eval { env := env' } f

/-- A u64-sorted witness-IR expression whose evaluation only depends on the
environment below `m`. -/
def U64Below (m : ℕ) (u : Witgen.U64Expr Fp) : Prop :=
  ∀ env env' : ProverEnvironment Fp, EnvAgree m env env' →
    Witgen.U64Expr.eval { env := env } u = Witgen.U64Expr.eval { env := env' } u

/-- A Boolean witness-IR condition whose evaluation only depends on the
environment below `m`. -/
def BBelow (m : ℕ) (b : Witgen.BExpr Fp) : Prop :=
  ∀ env env' : ProverEnvironment Fp, EnvAgree m env env' →
    Witgen.BExpr.eval { env := env } b = Witgen.BExpr.eval { env := env' } b

namespace FBelow

theorem expr {m : ℕ} {e : E} (h : Below m e) : FBelow m (.expr e) :=
  fun env env' hag => Below.eval_agree h env.toEnvironment env'.toEnvironment hag.1

theorem const (m : ℕ) (c : Fp) : FBelow m (.const c) := fun _ _ _ => rfl

theorem add {m : ℕ} {a b : Witgen.FExpr Fp} (ha : FBelow m a) (hb : FBelow m b) :
    FBelow m (a + b) := fun env env' hag => by
  show Witgen.FExpr.eval _ a + Witgen.FExpr.eval _ b =
    Witgen.FExpr.eval _ a + Witgen.FExpr.eval _ b
  rw [ha env env' hag, hb env env' hag]

theorem mul {m : ℕ} {a b : Witgen.FExpr Fp} (ha : FBelow m a) (hb : FBelow m b) :
    FBelow m (a * b) := fun env env' hag => by
  show Witgen.FExpr.eval _ a * Witgen.FExpr.eval _ b =
    Witgen.FExpr.eval _ a * Witgen.FExpr.eval _ b
  rw [ha env env' hag, hb env env' hag]

theorem inv {m : ℕ} {a : Witgen.FExpr Fp} (ha : FBelow m a) :
    FBelow m (Witgen.FExpr.inv a) := fun env env' hag => by
  show (Witgen.FExpr.eval _ a)⁻¹ = (Witgen.FExpr.eval _ a)⁻¹
  rw [ha env env' hag]

theorem neg {m : ℕ} {a : Witgen.FExpr Fp} (ha : FBelow m a) :
    FBelow m (Witgen.FExpr.neg a) := fun env env' hag => by
  show (-1 : Fp) * Witgen.FExpr.eval _ a = (-1 : Fp) * Witgen.FExpr.eval _ a
  rw [ha env env' hag]

theorem sub {m : ℕ} {a b : Witgen.FExpr Fp} (ha : FBelow m a) (hb : FBelow m b) :
    FBelow m (a - b) := fun env env' hag => by
  show Witgen.FExpr.eval _ a + (-1 : Fp) * Witgen.FExpr.eval _ b =
    Witgen.FExpr.eval _ a + (-1 : Fp) * Witgen.FExpr.eval _ b
  rw [ha env env' hag, hb env env' hag]

theorem ite {m : ℕ} {c : Witgen.BExpr Fp} {t e : Witgen.FExpr Fp}
    (hc : BBelow m c) (ht : FBelow m t) (he : FBelow m e) :
    FBelow m (.ite c t e) := fun env env' hag => by
  show (if Witgen.BExpr.eval _ c then Witgen.FExpr.eval _ t
      else Witgen.FExpr.eval _ e) =
    (if Witgen.BExpr.eval _ c then Witgen.FExpr.eval _ t
      else Witgen.FExpr.eval _ e)
  rw [hc env env' hag, ht env env' hag, he env env' hag]

theorem hintGet {m : ℕ} (key : String) (k : ℕ) {row : Witgen.U64Expr Fp} (col : Fin k)
    (h : U64Below m row) : FBelow m (.hintGet key k row col) := fun env env' hag => by
  show ((env.hint key k)[(Witgen.U64Expr.eval _ row).toNat]?.getD default)[col.val]'col.isLt =
    ((env'.hint key k)[(Witgen.U64Expr.eval _ row).toNat]?.getD default)[col.val]'col.isLt
  rw [h env env' hag, hag.2.1]

theorem dataGet {m : ℕ} (key : String) (k : ℕ) {row : Witgen.U64Expr Fp} (col : Fin k)
    (h : U64Below m row) : FBelow m (.dataGet key k row col) := fun env env' hag => by
  show ((env.data key k)[(Witgen.U64Expr.eval _ row).toNat]?.getD default)[col.val]'col.isLt =
    ((env'.data key k)[(Witgen.U64Expr.eval _ row).toNat]?.getD default)[col.val]'col.isLt
  rw [h env env' hag, hag.2.2]

end FBelow

namespace U64Below

theorem const (m : ℕ) (n : UInt64) : U64Below m (.const n) := fun _ _ _ => rfl

theorem val {m : ℕ} {x : Witgen.FExpr Fp} (h : FBelow m x) : U64Below m (.val x) :=
  fun env env' hag => by
    show UInt64.ofNat (FiniteField.val (Witgen.FExpr.eval _ x)) =
      UInt64.ofNat (FiniteField.val (Witgen.FExpr.eval _ x))
    rw [h env env' hag]

end U64Below

namespace BBelow

theorem bit {m : ℕ} {x : Witgen.FExpr Fp} (i : ℕ) (h : FBelow m x) :
    BBelow m (.bit x i) := fun env env' hag => by
  show (FiniteField.val (Witgen.FExpr.eval _ x)).testBit i =
    (FiniteField.val (Witgen.FExpr.eval _ x)).testBit i
  rw [h env env' hag]

end BBelow

/-! ## The operation certificate -/

/-- Every witness generator in `ops` (starting at offset `n`) only reads cells
below its own offset, and the hint provider and prover data. -/
def OpsCausal (n : ℕ) (ops : Operations Fp) : Prop :=
  ops.forAllFlat n { witness := fun m _ c =>
    ∀ env env' : ProverEnvironment Fp, EnvAgree m env env' → c.eval env = c.eval env' }

theorem cwOps_nil (n : ℕ) : OpsCausal n ([] : Operations Fp) := trivial

theorem cwOps_append (n : ℕ) (a b : Operations Fp) :
    OpsCausal n (a ++ b) ↔ OpsCausal n a ∧ OpsCausal (n + a.localLength) b := by
  simp only [OpsCausal, Operations.forAllFlat, Operations.forAll_append,
    Nat.add_comm a.localLength n]

@[simp] theorem operations_localLength {α : Type} (c : Circuit Fp α) (n : ℕ) :
    (c.operations n).localLength = c.localLength n := rfl

theorem cwOps_flatten_ofFn {k L n : ℕ} (g : Fin k → Operations Fp)
    (hlen : ∀ i, (g i).localLength = L) (h : ∀ i : Fin k, OpsCausal (n + i * L) (g i)) :
    OpsCausal n (List.ofFn g).flatten := by
  induction k generalizing n with
  | zero => simp only [List.ofFn_zero, List.flatten_nil]; exact cwOps_nil n
  | succ k ih =>
      rw [List.ofFn_succ, List.flatten_cons, cwOps_append, hlen 0]
      refine ⟨by simpa using h 0, ih (fun i => g i.succ) (fun i => hlen _) (fun i => ?_)⟩
      have := h i.succ
      rwa [Fin.val_succ, Nat.add_mul, Nat.one_mul, Nat.add_comm (↑i * L) L,
        ← Nat.add_assoc] at this

theorem cwOps_mapFinRange {β : Type} {m n : ℕ} [NeZero m] {body : Fin m → Circuit Fp β}
    {constant : Circuit.ConstantLength body}
    (h : ∀ i k, n ≤ k → OpsCausal k ((body i).operations k)) :
    OpsCausal n ((Circuit.mapFinRange m body constant).operations n) := by
  rw [Circuit.mapFinRange.operations_eq]
  refine cwOps_flatten_ofFn (L := constant.localLength) _ (fun i => ?_) (fun i => ?_)
  · simp only [operations_localLength]
    exact constant.localLength_eq i _
  · simp only [constant.localLength_eq]
    exact h i _ (by omega)

theorem cwOps_foldlRange {β : Type} {m n : ℕ} [Inhabited β] {init : β}
    {body : β → Fin m → Circuit Fp β}
    {constant : Circuit.ConstantLength fun (t : β × Fin m) => body t.1 t.2}
    (h : ∀ s i k, n ≤ k → OpsCausal k ((body s i).operations k)) :
    OpsCausal n ((Circuit.foldlRange m init body constant).operations n) := by
  rw [Circuit.foldlRange.operations_eq]
  refine cwOps_flatten_ofFn (L := constant.localLength) _ (fun i => ?_) (fun i => ?_)
  · simp only [operations_localLength]
    exact constant.localLength_eq (_, i) _
  · have hL : ∀ k, (body default i).localLength k = constant.localLength :=
      fun k => constant.localLength_eq (default, i) k
    simp only [hL]
    exact h _ i _ (by omega)

theorem cwOps_pure {α : Type} (a : α) (n : ℕ) :
    OpsCausal n ((pure a : Circuit Fp α).operations n) := by
  rw [Circuit.pure_operations_eq]
  exact cwOps_nil n

theorem cwOps_bind {α β : Type} {f : Circuit Fp α} {g : α → Circuit Fp β} {n : ℕ}
    (hf : OpsCausal n (f.operations n))
    (hg : OpsCausal (n + (f.operations n).localLength)
      ((g ((f n).1)).operations (n + (f.operations n).localLength))) :
    OpsCausal n ((f >>= g).operations n) := by
  rw [Circuit.bind_operations_eq]
  exact (cwOps_append _ _ _).mpr ⟨hf, hg⟩

theorem cwOps_map {α β : Type} {f : Circuit Fp α} {g : α → β} {n : ℕ}
    (hf : OpsCausal n (f.operations n)) : OpsCausal n ((g <$> f).operations n) := by
  rw [Circuit.map_operations_eq]
  exact hf

theorem cwOps_witnessField {n : ℕ} {f : Witgen.FExpr Fp} (h : FBelow n f) :
    OpsCausal n ((Circuit.witnessField f).operations n) := by
  show (∀ env env' : ProverEnvironment Fp, EnvAgree n env env' →
      (Witgen.WitgenIR.ofFExpr f).eval env = (Witgen.WitgenIR.ofFExpr f).eval env') ∧ True
  refine ⟨?_, trivial⟩
  intro env env' hag
  simp only [Witgen.WitgenIR.eval_ofFExpr]
  rw [h env env' hag]

theorem cwOps_assertZero (e : E) (n : ℕ) :
    OpsCausal n ((Circuit.assertZero e).operations n) := ⟨trivial, trivial⟩

theorem cwOps_witnessAssert {n : ℕ} {f : Witgen.FExpr Fp} (e : E) (h : FBelow n f) :
    OpsCausal n [Operation.witness 1 (.ofFExpr f), Operation.assert e] := by
  have hsplit : ([Operation.witness 1 (.ofFExpr f), Operation.assert e] : Operations Fp)
      = [Operation.witness 1 (.ofFExpr f)] ++ [Operation.assert e] := rfl
  rw [hsplit, cwOps_append]
  exact ⟨cwOps_witnessField h, cwOps_assertZero e _⟩

/-! ## `mat` and the lazy assertion -/

theorem matOut_below (e : E) : ∀ n, Below n e → Below (n + matLen e) (matOut e n) := by
  induction e with
  | var v => intro n h; exact Below.mono h (by simp only [matLen]; omega)
  | const c => intro n h; exact Below.const _ _
  | add a b iha ihb =>
      intro n h
      simp only [matOut, matLen]
      exact Below.add (Below.mono (iha n h.1) (by omega))
        (Below.mono (ihb (n + matLen a) (Below.mono h.2 (by omega))) (by omega))
  | mul a b iha ihb =>
      intro n h
      simp only [matOut, matLen]
      split
      · exact Below.mul (Below.mono (iha n h.1) (by omega))
          (Below.mono (ihb (n + matLen a) (Below.mono h.2 (by omega))) (by omega))
      · exact Below.var (by omega)

theorem matOps_causal (e : E) : ∀ n, Below n e → OpsCausal n (matOps e n) := by
  induction e with
  | var v => intro n h; exact cwOps_nil n
  | const c => intro n h; exact cwOps_nil n
  | add a b iha ihb =>
      intro n h
      simp only [matOps]
      rw [cwOps_append, matOps_localLength]
      exact ⟨iha n h.1, ihb (n + matLen a) (Below.mono h.2 (by omega))⟩
  | mul a b iha ihb =>
      intro n h
      simp only [matOps]
      rw [cwOps_append, matOps_localLength]
      refine ⟨iha n h.1, ?_⟩
      rw [cwOps_append, matOps_localLength]
      refine ⟨ihb (n + matLen a) (Below.mono h.2 (by omega)), ?_⟩
      split
      · exact cwOps_nil _
      · exact cwOps_witnessAssert _ (FBelow.mul
          (FBelow.expr (Below.mono (matOut_below a n h.1) (by omega)))
          (FBelow.expr (matOut_below b (n + matLen a) (Below.mono h.2 (by omega)))))

theorem mat_causal (e : E) (n : ℕ) (h : Below n e) :
    OpsCausal n ((mat e).operations n) := by
  rw [show (mat e).operations n = matOps e n from mat_operations_eq e n]
  exact matOps_causal e n h

theorem mat_output_below (e : E) (n : ℕ) (h : Below n e) :
    Below (n + matLen e) ((mat e n).1) := by
  rw [show (mat e n).1 = matOut e n from mat_output_eq e n]
  exact matOut_below e n h

theorem flat_below {n : ℕ} {c : Fp} {e : E} (h : Below n e) :
    ∀ it ∈ flat c e, Below n it.2 := by
  induction e generalizing c with
  | var v => intro it hit; simp only [flat, List.mem_singleton] at hit; subst hit; exact h
  | const cc => intro it hit; simp only [flat, List.mem_singleton] at hit; subst hit; exact h
  | add a b iha ihb =>
      intro it hit
      simp only [flat, List.mem_append] at hit
      rcases hit with h' | h'
      · exact iha h.1 it h'
      · exact ihb h.2 it h'
  | mul a b iha ihb =>
      intro it hit
      simp only [flat] at hit
      split at hit
      · exact ihb h.2 it hit
      · split at hit
        · exact iha h.1 it hit
        · simp only [List.mem_singleton] at hit; subst hit; exact h

theorem azlLoop_causal (acc : E) (l : List (Fp × E)) (n : ℕ) (hacc : Below n acc)
    (hl : ∀ it ∈ l, Below n it.2) : OpsCausal n ((azlLoop acc l).operations n) := by
  induction l generalizing acc n with
  | nil => exact cwOps_pure _ _
  | cons it rest ih =>
      obtain ⟨c, t⟩ := it
      simp only [azlLoop]
      refine cwOps_bind (mat_causal t n (hl (c, t) (by simp))) ?_
      simp only [operations_localLength, mat_localLength_eq]
      exact ih _ _ (Below.add (Below.mono hacc (by omega))
        (Below.sc c (mat_output_below t n (hl (c, t) (by simp)))))
        (fun it' hit' => Below.mono (hl it' (by simp [hit'])) (by omega))

theorem azlLoop_output_below (acc : E) (l : List (Fp × E)) (n : ℕ) (hacc : Below n acc)
    (hl : ∀ it ∈ l, Below n it.2) :
    Below (n + ((azlLoop acc l).operations n).localLength) ((azlLoop acc l n).1) := by
  induction l generalizing acc n with
  | nil =>
      show Below (n + ((pure acc : Circuit Fp E).operations n).localLength) acc
      simp only [Circuit.pure_operations_eq, Operations.localLength, Nat.add_zero]
      exact hacc
  | cons it rest ih =>
      obtain ⟨c, t⟩ := it
      simp only [azlLoop]
      show Below (n + (((mat t) >>= fun w => azlLoop (acc + sc c w) rest).operations n).localLength)
        (((mat t) >>= fun w => azlLoop (acc + sc c w) rest) n).1
      rw [Circuit.bind_operations_eq, Operations.append_localLength]
      rw [show ((mat t >>= fun w => azlLoop (acc + sc c w) rest) n).1
          = ((mat t >>= fun w => azlLoop (acc + sc c w) rest).output n) from rfl,
        Circuit.bind_output_eq]
      simp only [operations_localLength, mat_localLength_eq, ← Nat.add_assoc]
      exact ih _ _ (Below.add (Below.mono hacc (by omega))
        (Below.sc c (mat_output_below t n (hl (c, t) (by simp)))))
        (fun it' hit' => Below.mono (hl it' (by simp [hit'])) (by omega))

theorem azlLinLoop_causal (acc : E) (l : List (Fp × E)) (n : ℕ) (hacc : Below n acc)
    (hl : ∀ it ∈ l, Below n it.2) : OpsCausal n ((azlLinLoop acc l).operations n) := by
  induction l generalizing acc n with
  | nil => exact cwOps_pure _ _
  | cons it rest ih =>
      obtain ⟨c, t⟩ := it
      simp only [azlLinLoop]
      exact ih _ _ (Below.add hacc (Below.sc c (hl (c, t) (by simp))))
        (fun it' hit' => hl it' (by simp [hit']))

theorem assertZeroLazy_causal (e : E) (n : ℕ) (he : Below n e) :
    OpsCausal n ((assertZeroLazy e).operations n) := by
  simp only [assertZeroLazy]
  cases h : (flat 1 e).filter (fun it => isProd it.2) with
  | nil => simp only [h]; exact cwOps_assertZero _ _
  | cons it rest =>
      obtain ⟨c, t⟩ := it
      cases t with
      | mul a b =>
          have hmem : (c, Expression.mul a b) ∈ (flat 1 e).filter (fun it => isProd it.2) := by
            rw [h]; simp
          have hmem' := List.mem_of_mem_filter hmem
          have ha : Below n a := (flat_below he _ hmem').1
          have hb : Below n b := (flat_below he _ hmem').2
          simp only [h]
          refine cwOps_bind (mat_causal a n ha) ?_
          simp only [operations_localLength, mat_localLength_eq]
          refine cwOps_bind (mat_causal b _ (Below.mono hb (by omega))) ?_
          simp only [operations_localLength, mat_localLength_eq]
          refine cwOps_bind (azlLoop_causal _ _ _ ?_ ?_) ?_
          · exact Below.sc c (Below.mul
              (Below.mono (mat_output_below a n ha)
                (show n + matLen a ≤ n + matLen a + matLen b by omega))
              (mat_output_below b (n + matLen a) (Below.mono hb (by omega))))
          · intro it' hit'
            exact Below.mono (flat_below he it' (by
              have : it' ∈ (flat 1 e).filter (fun it => isProd it.2) := by
                rw [h]; simp [hit']
              exact List.mem_of_mem_filter this)) (by omega)
          · refine cwOps_bind (azlLinLoop_causal _ _ _ ?_ ?_) ?_
            · exact azlLoop_output_below (sc c ((mat a n).1 * (mat b (n + matLen a)).1)) rest
                (n + matLen a + matLen b)
                (Below.sc c (Below.mul
                  (Below.mono (mat_output_below a n ha)
                    (show n + matLen a ≤ n + matLen a + matLen b by omega))
                  (mat_output_below b (n + matLen a) (Below.mono hb (by omega)))))
                (fun it' hit' => Below.mono (flat_below he it' (by
                  have : it' ∈ (flat 1 e).filter (fun it => isProd it.2) := by
                    rw [h]; simp [hit']
                  exact List.mem_of_mem_filter this)) (by omega))
            · intro it' hit'
              exact Below.mono (flat_below he it' (by
                have : it' ∈ (flat 1 e).filter (fun it => !isProd it.2) := by
                  simp only [List.mem_filter] at hit' ⊢
                  exact ⟨hit'.1, by simpa using hit'.2⟩
                exact List.mem_of_mem_filter this)) (by omega)
            · exact cwOps_assertZero _ _
      | var v => simp only [h]; exact cwOps_pure _ _
      | const cc => simp only [h]; exact cwOps_pure _ _
      | add x y => simp only [h]; exact cwOps_pure _ _

end StandardECDSA
