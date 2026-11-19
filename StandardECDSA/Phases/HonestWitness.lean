/-
# Honest-witness row lemmas (gaps G1 / G2)

`ConstraintsHold.Completeness` and `ConstraintsHold.Soundness` differ only in
their `lookup` and `subcircuit` clauses.  For a gadget that emits neither, the
two are the same proposition, so the existing `*_complete` lemmas of
`StandardECDSA/Main.lean` can be re-read as `Soundness` lemmas.

That re-reading is what the honest-witness induction of gap G1 needs: the
induction has to know that the *honest prover's* rows hold, and the honest
prover's wire values are pinned by
`ProverEnvironment.UsesLocalWitnessesCompleteness` (`Clean/Circuit/Basic.lean`),
which says that every `.witness m c` operation at offset `o` satisfies
`env.ExtendsVector (c.eval env) o`, i.e. the wires hold exactly the evaluated
hint expressions.

The lemmas below therefore prove, for each gadget of the three arithmetic
phases, that

```text
UsesLocalWitnessesCompleteness env n (g.operations n)  →  ConstraintsHold.Soundness env (g.operations n)
```

with exactly the extra hypotheses that the gadget's *guarded* denominators
require (`affAdd`/`elm`/`elmCore` need `x(q) - x(p) ≠ 0` and, for the ELM
family, `x(p) - xu ≠ 0`; `affDouble` needs `y(p) ≠ 0`).

`elmTo` is deliberately absent: its last two rows are the *assertion* being
checked, not witness definitions, so they cannot be derived from
`UsesLocalWitnessesCompleteness`.  Only its `elmCore` prefix is available here.

`mat_soundness_of_ulwc` re-runs the `mat_complete` induction with
`ConstraintsHold.Soundness` (the two predicates agree on `matOps`, which emits
only `.witness`/`.assert`), which is what `affDouble_soundness_of_ulwc` needs.

Task T13 / gaps G1, G2.
-/

import StandardECDSA.Phases.FixedBaseSemantics
import StandardECDSA.Phases.LadderSemantics
import StandardECDSA.Phases.TableSemantics
import StandardECDSA.Gadgets.Semantics2

namespace StandardECDSA.Phases

open StandardECDSA StandardECDSA.Gadgets

/-! ## Re-assembling soundness

`soundness_append` and `soundness_bind` *split* a soundness hypothesis.  The
honest-witness induction needs the converse, so the two `_intro` lemmas below
re-assemble the halves.  They are stated with the halves as explicit variables
for the same reason as `soundness_append`: writing them inline makes `whnf`
reduce the left half to a concrete `cons` list and lose the append structure.
-/

/-- Re-assemble the soundness of an appended operation list. -/
theorem soundness_append_intro (env : Environment Fp) (A B : Operations Fp)
    (h1 : ConstraintsHold.Soundness env A)
    (h2 : B.forAllNoOffset (soundnessCond env)) :
    ConstraintsHold.Soundness env (A ++ B) := by
  simp only [ConstraintsHold.Soundness, Operations.forAllNoOffset_append]
  exact ⟨h1, h2⟩

/-- Re-assemble the soundness of a `>>=`-composed circuit. -/
theorem soundness_bind_intro {α β : Type} (env : Environment Fp) (c : C α) (f : α → C β) (n : ℕ)
    (h1 : ConstraintsHold.Soundness env (c.operations n))
    (h2 : ConstraintsHold.Soundness env ((f (c.output n)).operations (n + c.localLength n))) :
    ConstraintsHold.Soundness env ((c >>= f).operations n) := by
  simp only [ConstraintsHold.Soundness, Circuit.operations, Circuit.output, Circuit.localLength,
    bind_snd, Operations.forAllNoOffset_append]
  exact ⟨h1, h2⟩

/-! ## Field-level gadgets -/

/-- The `muxConst4W` rows hold for the honest witness. -/
theorem muxConst4W_soundness_of_ulwc (b0 b1 : E) (tab : Array (Fp × Fp))
    (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((muxConst4W b0 b1 tab).operations n)) :
    ConstraintsHold.Soundness env ((muxConst4W b0 b1 tab).operations n) := by
  simp only [muxConst4W, circuit_norm, pm] at hw ⊢
  rw [hw]; ring

/-- The `selW` rows hold for the honest witness. -/
theorem selW_soundness_of_ulwc (b x0 x1 : E) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((selW b x0 x1).operations n)) :
    ConstraintsHold.Soundness env ((selW b x0 x1).operations n) := by
  simp only [selW, circuit_norm, pm] at hw ⊢
  rw [hw]; ring

/-- The `mux4W` rows hold for the honest witness. -/
theorem mux4W_soundness_of_ulwc (b0 b1 : E) (p0 p1 p2 p3 : Pt)
    (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((mux4W b0 b1 p0 p1 p2 p3).operations n)) :
    ConstraintsHold.Soundness env ((mux4W b0 b1 p0 p1 p2 p3).operations n) := by
  simp only [mux4W, selW, circuit_norm, pm] at hw ⊢
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hw
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]; ring
  · rw [e2]; ring
  · rw [e3]; ring
  · rw [e4]; ring
  · rw [e5]; ring
  · rw [e6]; ring

/-! ## The `mat` gadget

`matOps` emits only `.witness` and `.assert`, so `ConstraintsHold.Completeness`
and `ConstraintsHold.Soundness` agree on it.  Rather than bridge the two
predicates (which would need the `NoLookupSub` facts for `matOps`, and those
live in a file that imports `Main.lean`), the induction of `mat_complete` is
simply re-run with `Soundness`.
-/

/-- The `mat` rows hold for the honest witness. -/
theorem mat_soundness_of_ulwc (e : E) : ∀ n (env : ProverEnvironment Fp),
    env.UsesLocalWitnessesCompleteness n (matOps e n) →
    ConstraintsHold.Soundness env (matOps e n) := by
  induction e with
  | var v =>
      intro n env _
      rw [matOps]
      simp [ConstraintsHold.Soundness, Operations.forAllNoOffset]
  | const k =>
      intro n env _
      rw [matOps]
      simp [ConstraintsHold.Soundness, Operations.forAllNoOffset]
  | add a b iha ihb =>
      intro n env h
      rw [matOps, ulwc_append] at h
      rw [matOps_localLength] at h
      rw [matOps, ConstraintsHold.Soundness, Operations.forAllNoOffset_append]
      exact ⟨iha n env h.1, ihb (n + matLen a) env h.2⟩
  | mul a b iha ihb =>
      intro n env h
      by_cases hc : deg a = 0 ∨ deg b = 0
      · simp only [matOps, hc, if_true, List.append_nil] at h ⊢
        rw [ulwc_append] at h
        rw [matOps_localLength] at h
        rw [ConstraintsHold.Soundness, Operations.forAllNoOffset_append]
        exact ⟨iha n env h.1, ihb (n + matLen a) env h.2⟩
      · simp only [matOps, hc, if_false] at h ⊢
        rw [ulwc_append] at h
        rw [matOps_localLength] at h
        obtain ⟨h1, h2⟩ := h
        rw [ulwc_append] at h2
        rw [matOps_localLength] at h2
        obtain ⟨h2a, h2b⟩ := h2
        rw [ConstraintsHold.Soundness, Operations.forAllNoOffset_append]
        refine ⟨iha n env h1, ?_⟩
        rw [Operations.forAllNoOffset_append]
        refine ⟨ihb (n + matLen a) env h2a, ?_⟩
        simp only [Operations.forAllNoOffset, ProverEnvironment.UsesLocalWitnessesCompleteness]
          at h2b ⊢
        exact ⟨trivial, mat_assert_eval a b n env h2b.1, trivial⟩

/-! ## Affine gadgets -/

/-- The `affAdd` rows hold for the honest witness, provided the guarded
denominator `x(q) - x(p)` is nonzero. -/
theorem affAdd_soundness_of_ulwc (p q : Pt) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((affAdd p q).operations n))
    (hDx : Expression.eval env.toEnvironment q.1 - Expression.eval env.toEnvironment p.1 ≠ 0) :
    ConstraintsHold.Soundness env ((affAdd p q).operations n) := by
  simp only [affAdd, nonzero, circuit_norm, pm] at hw ⊢
  obtain ⟨e1, e2, e3, e4⟩ := hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1]; simp only [eval_cst]; linear_combination mul_inv_cancel₀ hDx
  · rw [e2, e1]; field_simp; ring
  · rw [e3]; ring
  · rw [e4]; ring

/-- The `affDouble` rows hold for the honest witness, provided `y(p) ≠ 0`. -/
theorem affDouble_soundness_of_ulwc (p : Pt) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((affDouble p).operations n))
    (hy : Expression.eval env.toEnvironment p.2 ≠ 0) :
    ConstraintsHold.Soundness env ((affDouble p).operations n) := by
  simp only [affDouble, mm, circuit_norm, pm] at hw ⊢
  obtain ⟨e1, e2, e3, e4⟩ := hw
  rw [mat_operations_eq] at e1
  have hlen : Operations.localLength (mat (.mul p.1 p.1) n).2 = matLen (.mul p.1 p.1) :=
    mat_localLength_eq _ n
  simp only [hlen] at e2 e3 e4 ⊢
  rw [Nat.add_comm (matLen (.mul p.1 p.1)) n] at e2 e3 e4
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mat_operations_eq]
    exact mat_soundness_of_ulwc _ n env e1
  · have h2 : (2 : Fp) ≠ 0 := by decide
    have hsc : Expression.eval env.toEnvironment (sc 2 p.2) ≠ 0 := by
      simp only [sc, circuit_norm]
      exact mul_ne_zero h2 hy
    rw [e2]
    field_simp
    ring
  · rw [e3]; ring
  · rw [e4]; ring

/-! ## ELM gadgets -/

/-- The `elmCore` rows hold for the honest witness, provided both denominators
`x(q) - x(p)` and `x(p) - xu` are nonzero. -/
theorem elmCore_soundness_of_ulwc (p q : Pt) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((elmCore p q).operations n))
    (hDx : Expression.eval env.toEnvironment q.1 - Expression.eval env.toEnvironment p.1 ≠ 0)
    (hDx2 : Expression.eval env.toEnvironment p.1 - env.get (n + 2) ≠ 0) :
    ConstraintsHold.Soundness env ((elmCore p q).operations n) := by
  simp only [elmCore, nonzero, circuit_norm, pm] at hw ⊢
  obtain ⟨e1, e2, e3, e4⟩ := hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1]; simp only [eval_cst]; linear_combination mul_inv_cancel₀ hDx
  · rw [e2, e1]; field_simp; ring
  · rw [e3]; ring
  · rw [e4]; field_simp; ring

/-- The `elm` rows hold for the honest witness, provided both denominators are
nonzero. -/
theorem elm_soundness_of_ulwc (p q : Pt) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((elm p q).operations n))
    (hDx : Expression.eval env.toEnvironment q.1 - Expression.eval env.toEnvironment p.1 ≠ 0)
    (hDx2 : Expression.eval env.toEnvironment p.1 - env.get (n + 2) ≠ 0) :
    ConstraintsHold.Soundness env ((elm p q).operations n) := by
  simp only [elm, elmCore, nonzero, circuit_norm, pm] at hw ⊢
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hw
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]; simp only [eval_cst]; linear_combination mul_inv_cancel₀ hDx
  · rw [e2, e1]; field_simp; ring
  · rw [e3]; ring
  · rw [e4]; field_simp; ring
  · rw [e5]; ring
  · rw [e6]; ring

/-- The `shiftedTables` rows hold for the honest witness, provided the five
guarded denominators are nonzero. -/
theorem shiftedTables_soundness_of_ulwc (h q r : Pt) (env : ProverEnvironment Fp) (n : Nat)
    (hw : env.UsesLocalWitnessesCompleteness n ((shiftedTables h q r).operations n))
    (hdeg : deg h.1 = 1)
    (hy : Expression.eval env h.2 ≠ 0)
    (hdx1 : Expression.eval env h.1 - env.get (n + 2) ≠ 0)
    (hdx2 : Expression.eval env q.1 - env.get (n + 6) ≠ 0)
    (hdx3 : Expression.eval env r.1 - env.get (n + 6) ≠ 0)
    (hdx4 : Expression.eval env r.1 - env.get (n + 10) ≠ 0)
    (hdx5 : Expression.eval env r.1 - env.get (n + 22) ≠ 0) :
    ConstraintsHold.Soundness env ((shiftedTables h q r).operations n) := by
  simp only [shiftedTables, circuit_norm] at hw ⊢
  simp only [affAdd_localLength', affDouble_localLength' hdeg, Nat.add_comm 4] at hw ⊢
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := hw
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact affDouble_soundness_of_ulwc h env n w1 hy
  · exact affAdd_soundness_of_ulwc _ _ env _ w2 (by rw [affDouble_out_fst hdeg]; exact hdx1)
  · exact affAdd_soundness_of_ulwc _ _ env _ w3 (by rw [affAdd_out_fst]; exact hdx2)
  · exact affAdd_soundness_of_ulwc _ _ env _ w4 (by rw [affAdd_out_fst]; exact hdx3)
  · exact affAdd_soundness_of_ulwc _ _ env _ w5 (by rw [affAdd_out_fst]; exact hdx4)
  · exact affAdd_soundness_of_ulwc _ _ env _ w6 hdx2
  · exact affAdd_soundness_of_ulwc _ _ env _ w7 hdx3
  · exact affAdd_soundness_of_ulwc _ _ env _ w8 (by rw [affAdd_out_fst]; exact hdx5)

/-! ## Phase bodies

The two lemmas below take the `UsesLocalWitnessesCompleteness` facts of the two
halves separately: the caller splits the phase-level hypothesis with the
existing `ulwc_append` / `Circuit.foldlRange.usesLocalWitnesses` machinery, so
these lemmas never have to `whnf` a `>>=` or a fold.
-/

/-- One fixed-base window's rows hold for the honest witness. -/
theorem fixedBaseBody_soundness_of_ulwc (eb : Vector E 256) (ep : Pt) (i : Fin 128)
    (env : ProverEnvironment Fp) (n : Nat)
    (hw1 : env.UsesLocalWitnessesCompleteness n
      ((fbMux eb StandardECDSA.Math.FixedTables.fixedTables i).operations n))
    (hw2 : env.UsesLocalWitnessesCompleteness (n + 1)
      ((affAdd ep ((fbMux eb StandardECDSA.Math.FixedTables.fixedTables i).output n)).operations
        (n + 1)))
    (hDx : Expression.eval env.toEnvironment
        ((fbMux eb StandardECDSA.Math.FixedTables.fixedTables i).output n).1
      - Expression.eval env.toEnvironment ep.1 ≠ 0) :
    ConstraintsHold.Soundness env
      ((fixedBaseBody eb StandardECDSA.Math.FixedTables.fixedTables ep i).operations n) := by
  rw [fixedBaseBody_eq]
  refine soundness_bind_intro env _ _ _ (muxConst4W_soundness_of_ulwc _ _ _ env n hw1) ?_
  rw [show Circuit.localLength (fbMux eb StandardECDSA.Math.FixedTables.fixedTables i) n = 1 from by
    simp only [fbMux]; exact muxConst4W_localLength _ _ _ _]
  exact affAdd_soundness_of_ulwc ep _ env _ hw2 hDx

/-- One ladder step's rows hold for the honest witness. -/
theorem jointLadderBody_soundness_of_ulwc (tables : Tables) (rb sb : Vector E 256)
    (acc : Pt) (j : Fin 255) (env : ProverEnvironment Fp) (n : Nat)
    (hw1 : env.UsesLocalWitnessesCompleteness n
      ((mux4W (rb.get ⟨255 - j.val, by omega⟩) (sb.get ⟨255 - j.val, by omega⟩)
        (tables.x0 j.val) (tables.x1 j.val) (tables.x2 j.val)
        (tables.x3 j.val)).operations n))
    (hw2 : env.UsesLocalWitnessesCompleteness
      (n + Circuit.localLength (mux4W (rb.get ⟨255 - j.val, by omega⟩)
        (sb.get ⟨255 - j.val, by omega⟩) (tables.x0 j.val) (tables.x1 j.val)
        (tables.x2 j.val) (tables.x3 j.val)) n)
      ((elm acc ((mux4W (rb.get ⟨255 - j.val, by omega⟩) (sb.get ⟨255 - j.val, by omega⟩)
        (tables.x0 j.val) (tables.x1 j.val) (tables.x2 j.val)
        (tables.x3 j.val)).output n)).operations
        (n + Circuit.localLength (mux4W (rb.get ⟨255 - j.val, by omega⟩)
          (sb.get ⟨255 - j.val, by omega⟩) (tables.x0 j.val) (tables.x1 j.val)
          (tables.x2 j.val) (tables.x3 j.val)) n)))
    (hDx : Expression.eval env.toEnvironment
        ((mux4W (rb.get ⟨255 - j.val, by omega⟩) (sb.get ⟨255 - j.val, by omega⟩)
          (tables.x0 j.val) (tables.x1 j.val) (tables.x2 j.val)
          (tables.x3 j.val)).output n).1
      - Expression.eval env.toEnvironment acc.1 ≠ 0)
    (hDx2 : Expression.eval env.toEnvironment acc.1
      - env.get (n + Circuit.localLength (mux4W (rb.get ⟨255 - j.val, by omega⟩)
          (sb.get ⟨255 - j.val, by omega⟩) (tables.x0 j.val) (tables.x1 j.val)
          (tables.x2 j.val) (tables.x3 j.val)) n + 2) ≠ 0) :
    ConstraintsHold.Soundness env ((jointLadderBody tables rb sb acc j).operations n) := by
  rw [jointLadderBody_ops]
  exact soundness_append_intro env _ _
    (mux4W_soundness_of_ulwc _ _ _ _ _ _ env n hw1)
    (elm_soundness_of_ulwc acc _ env _ hw2 hDx hDx2)

end StandardECDSA.Phases
