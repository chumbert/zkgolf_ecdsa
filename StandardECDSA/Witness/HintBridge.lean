/-
# The hint-get evaluation bridge (gap G2, step 2)

`StandardECDSA/Witness/Hint.lean` builds the concrete `ProverHint` of a seed.
This module proves that the *wires* the circuit allocates for its hints really
carry those cells, i.e. it connects

* `ProverEnvironment.UsesLocalWitnessesCompleteness` (the completeness-side
  hypothesis: every `witness` operation's value is the one its generator
  computes), and
* `Witgen.FExpr.eval` on the `.hintGet` leaf that `StandardECDSA.hint` builds,

to the 772-cell list `seedCells s`.

## Why this is not a `simp` step

`UsesLocalWitnessesCompleteness` is a `def` that pattern-matches on the operation
list, so it can only be decomposed structurally.  The circuit's hint wires are
allocated by

* `seedPhase` — four `hint i` leaves at offsets `n, n+1, n+2, n+3`;
* `bitsPhase` — three `bitVec base stride` stages, each a `mapFinRange 256` of a
  `bitBody` that allocates one `hint (base + stride·k)` wire.

The two generic decompositions are `ulwc_append_left` (split a concatenation) and
`ulwc_flatten_ofFn` (split a `mapFinRange`'s flattened operation list), and
`hint_ulwc` reads a single hint wire.

## Main results

* `hint_ulwc` — a single hint wire carries the hint table's cell;
* `bitVec_ulwc` — the 256 wires of a `bitVec` carry hint rows `base + stride·k`;
* `seedPhase_ulwc`, `bitsPhase_ulwc` — the two hint-allocating stages;
* `main_ulwc_seed_bits` — those two stages inherit `main`'s local witnesses;
* `main_hint_cells` — **the 772 hint wires of `main` are exactly `seedCells s`**;
* `seedPhase_out_ry/hx/hy/overflow` — the seed stage's output expressions are the
  corresponding wires, so `Expression.eval` of them is a seed cell.

Gap G2 of `docs/m6-report.md`.
-/
import StandardECDSA.Main
import StandardECDSA.Witness.Hint

namespace StandardECDSA

open Circuit
open StandardECDSA.Gadgets
open StandardECDSA.Phases
open StandardECDSA.Math
open StandardECDSA.Witness

/-! ## The hint leaf -/

/-- A `hint i` leaf allocates exactly one wire and one witness operation. -/
theorem hint_ops (i n : Nat) :
    (hint i).operations n
      = [Operation.witness 1 (Witgen.WitgenIR.ofFExpr
          (.hintGet hintKey 1 (.const i.toUInt64) ⟨0, by decide⟩))] := by
  simp only [hint, witnessField, Circuit.operations]

/-- A `hint i` leaf's output is the wire it allocates. -/
theorem hint_out (i n : Nat) : (hint i).output n = Expression.var (F := Fp) ⟨n⟩ := by
  simp only [hint, output_witnessField]

theorem hint_localLength (i n : Nat) : ((hint i).operations n).localLength = 1 := by
  rw [hint_ops]
  rfl

/-- `UsesLocalWitnessesCompleteness` on a single witness operation. -/
theorem ulwc_single (env : ProverEnvironment Fp) (c : Witgen.WitgenIR Fp 1) (n : Nat) :
    env.UsesLocalWitnessesCompleteness n [Operation.witness 1 c]
      ↔ env.get n = (c.eval env)[0] := by
  simp only [ProverEnvironment.UsesLocalWitnessesCompleteness, ProverEnvironment.ExtendsVector,
    and_true]
  constructor
  · intro h; exact h 0
  · intro h i; simpa using h

theorem toUInt64_toNat_of_lt {i : Nat} (hi : i < 2^64) : i.toUInt64.toNat = i := by
  simp only [Nat.toUInt64, UInt64.toNat, UInt64.ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

/-- **A hint wire carries the hint table's cell.** -/
theorem hint_ulwc (env : ProverEnvironment Fp) (i n : Nat) (hi : i < 2^64)
    (h : env.UsesLocalWitnessesCompleteness n ((hint i).operations n)) :
    env.get n = ((env.hint hintKey 1)[i]?.getD default)[0] := by
  rw [hint_ops] at h
  rw [ulwc_single] at h
  rw [h]
  rw [Witgen.WitgenIR.getElem_eval_ofFExpr]
  simp only [Witgen.FExpr.eval, Witgen.U64Expr.eval, toUInt64_toNat_of_lt hi]

/-! ## Splitting the local-witness hypothesis -/

/-- Split `UsesLocalWitnessesCompleteness` over a concatenation, with the offset
of the tail written as `n + as.localLength`. -/
theorem ulwc_append_left {as bs : Operations Fp} {env : ProverEnvironment Fp} {n : Nat}
    (h : env.UsesLocalWitnessesCompleteness n (as ++ bs)) :
    env.UsesLocalWitnessesCompleteness n as ∧
      env.UsesLocalWitnessesCompleteness (n + as.localLength) bs := by
  have h' := (ConstraintsHold.append_localWitnesses (as := as) (bs := bs) (env_p := env) n).mp h
  exact ⟨h'.1, by rw [Nat.add_comm]; exact h'.2⟩

/-- Split `UsesLocalWitnessesCompleteness` over a flattened `Fin k` family. -/
theorem ulwc_flatten_ofFn {k L : Nat} (g : Fin k → Operations Fp)
    (hlen : ∀ i, (g i).localLength = L) (env : ProverEnvironment Fp) (n : Nat)
    (h : env.UsesLocalWitnessesCompleteness n (List.ofFn g).flatten) :
    ∀ i : Fin k, env.UsesLocalWitnessesCompleteness (n + i.val * L) (g i) := by
  induction k generalizing n with
  | zero => intro i; exact i.elim0
  | succ k ih =>
    rw [List.ofFn_succ, List.flatten_cons, ConstraintsHold.append_localWitnesses] at h
    rw [hlen 0, Nat.add_comm L n] at h
    intro i
    rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨j, rfl⟩
    · subst h0
      simpa using h.1
    · have h2 := ih (fun i => g i.succ) (fun i => hlen _) (n := n + L) h.2 j
      have he : n + (j.succ).val * L = (n + L) + j.val * L := by
        simp only [Fin.val_succ]; ring
      rw [he]
      exact h2

/-! ## The bit bodies and bit vectors -/

/-- One `bitBody` wire carries hint row `base + stride·i`. -/
theorem bitBody_ulwc (base stride : Nat) (i : Fin 256) (env : ProverEnvironment Fp) (n : Nat)
    (hi : base + stride * i.val < 2^64)
    (h : env.UsesLocalWitnessesCompleteness n ((bitBody base stride i).operations n)) :
    env.get n = ((env.hint hintKey 1)[base + stride * i.val]?.getD default)[0] := by
  rw [bitBody_ops] at h
  rw [ConstraintsHold.append_localWitnesses] at h
  exact hint_ulwc env _ n hi h.1

/-- **The 256 wires of a `bitVec` carry hint rows `base + stride·k`.** -/
theorem bitVec_ulwc (base stride : Nat) (env : ProverEnvironment Fp) (n : Nat)
    (hi : ∀ k : Fin 256, base + stride * k.val < 2^64)
    (h : env.UsesLocalWitnessesCompleteness n ((bitVec base stride).operations n)) :
    ∀ k : Fin 256,
      env.get (n + k.val) = ((env.hint hintKey 1)[base + stride * k.val]?.getD default)[0] := by
  rw [bitVec, Circuit.mapFinRange.operations_eq, bitBody_localLength] at h
  have hL : ∀ i : Fin 256, ((bitBody base stride i).operations (n + i.val * 1)).localLength = 1 := by
    intro i
    show (bitBody base stride i).localLength (n + i.val * 1) = 1
    exact (bitBody_constantLength base stride).localLength_eq i _
  have hsplit := ulwc_flatten_ofFn
    (fun i : Fin 256 => (bitBody base stride i).operations (n + i.val * 1)) hL env n h
  intro k
  have hk := hsplit k
  rw [show n + k.val * 1 = n + k.val from by ring] at hk
  exact bitBody_ulwc base stride k env (n + k.val) (hi k) hk

/-! ## The two hint-allocating stages -/

/-- The seed stage's four hint wires. -/
theorem seedPhase_ulwc (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (h : env.UsesLocalWitnessesCompleteness n ((seedPhase inp).operations n)) :
    env.get n = ((env.hint hintKey 1)[0]?.getD default)[0] ∧
      env.get (n + 1) = ((env.hint hintKey 1)[1]?.getD default)[0] ∧
      env.get (n + 2) = ((env.hint hintKey 1)[2]?.getD default)[0] ∧
      env.get (n + 3) = ((env.hint hintKey 1)[3]?.getD default)[0] := by
  rw [seedPhase_ops] at h
  simp only [List.append_assoc] at h
  obtain ⟨h0, h⟩ := ulwc_append_left h
  rw [hint_localLength] at h
  obtain ⟨h1, h⟩ := ulwc_append_left h
  rw [hint_localLength] at h
  obtain ⟨h2, h⟩ := ulwc_append_left h
  rw [hint_localLength] at h
  obtain ⟨h3, -⟩ := ulwc_append_left h
  exact ⟨hint_ulwc env 0 n (by decide) h0, hint_ulwc env 1 (n + 1) (by decide) h1,
    hint_ulwc env 2 (n + 2) (by decide) h2, hint_ulwc env 3 (n + 3) (by decide) h3⟩

/-- The bits stage's 768 hint wires. -/
theorem bitsPhase_ulwc (env : ProverEnvironment Fp) (n : Nat)
    (h : env.UsesLocalWitnessesCompleteness n ((bitsPhase).operations n)) :
    (∀ k : Fin 256,
        env.get (n + k.val) = ((env.hint hintKey 1)[4 + 3 * k.val]?.getD default)[0]) ∧
      (∀ k : Fin 256,
        env.get (n + 256 + k.val) = ((env.hint hintKey 1)[5 + 3 * k.val]?.getD default)[0]) ∧
      (∀ k : Fin 256,
        env.get (n + 512 + k.val) = ((env.hint hintKey 1)[6 + 3 * k.val]?.getD default)[0]) := by
  rw [bitsPhase_ops] at h
  simp only [List.append_assoc] at h
  obtain ⟨h0, h⟩ := ulwc_append_left h
  rw [show ((bitVec 4 3).operations n).localLength = 256 from bitVec_localLength 4 3 n] at h
  obtain ⟨h1, h⟩ := ulwc_append_left h
  rw [show ((bitVec 5 3).operations (n + 256)).localLength = 256 from
    bitVec_localLength 5 3 (n + 256)] at h
  have h2 : env.UsesLocalWitnessesCompleteness (n + 512) ((bitVec 6 3).operations (n + 512)) := by
    rw [show n + 512 = n + 256 + 256 from by ring]; exact h
  refine ⟨fun k => bitVec_ulwc 4 3 env n (fun k => by omega) h0 k, ?_, ?_⟩
  · intro k
    have := bitVec_ulwc 5 3 env (n + 256) (fun k => by omega) h1 k
    rwa [show n + 256 + k.val = (n + 256) + k.val from by ring] at this
  · intro k
    have := bitVec_ulwc 6 3 env (n + 512) (fun k => by omega) h2 k
    rwa [show n + 512 + k.val = (n + 512) + k.val from by ring] at this

/-- The seed and bits stages of `main` inherit the local-witness property. -/
theorem main_ulwc_seed_bits (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (h : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    env.UsesLocalWitnessesCompleteness n ((seedPhase inp n).2) ∧
      env.UsesLocalWitnessesCompleteness (off3 inp n) ((bitsPhase (off3 inp n)).2) := by
  rw [main_ops'] at h
  simp only [List.append_assoc] at h
  obtain ⟨h1, h⟩ := ulwc_append_left h
  obtain ⟨-, h⟩ := ulwc_append_left h
  obtain ⟨-, h⟩ := ulwc_append_left h
  obtain ⟨h4, -⟩ := ulwc_append_left h
  exact ⟨h1, h4⟩

/-! ## The 772 hint cells of `main` -/

/-- **The 772 hint wires of `main` are exactly the seed cells.**

For an environment whose hint provider is `seedHint s` and which supplies the local
witnesses of `main`, the wires allocated by the seed and bits stages carry exactly
the 772 cells of `s`, in the layout the circuit reads them. -/
theorem main_hint_cells (inp : Var Input Fp) (s : Witness.Seed) (env : ProverEnvironment Fp)
    (n : Nat) (hhint : env.hint = seedHint s)
    (h : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    env.get n = (seedCells s).getD 0 0 ∧
      env.get (n + 1) = (seedCells s).getD 1 0 ∧
      env.get (n + 2) = (seedCells s).getD 2 0 ∧
      env.get (n + 3) = (seedCells s).getD 3 0 ∧
      (∀ k : Fin 256,
        env.get (off3 inp n + k.val) = (seedCells s).getD (4 + 3 * k.val) 0) ∧
      (∀ k : Fin 256,
        env.get (off3 inp n + 256 + k.val) = (seedCells s).getD (5 + 3 * k.val) 0) ∧
      (∀ k : Fin 256,
        env.get (off3 inp n + 512 + k.val) = (seedCells s).getD (6 + 3 * k.val) 0) := by
  obtain ⟨h1, h4⟩ := main_ulwc_seed_bits inp env n h
  obtain ⟨h0, h1', h2, h3⟩ := seedPhase_ulwc inp env n h1
  obtain ⟨hb0, hb1, hb2⟩ := bitsPhase_ulwc env (off3 inp n) h4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0, hhint]; exact seedHint_getElem s 0 (by decide) 0
  · rw [h1', hhint]; exact seedHint_getElem s 1 (by decide) 0
  · rw [h2, hhint]; exact seedHint_getElem s 2 (by decide) 0
  · rw [h3, hhint]; exact seedHint_getElem s 3 (by decide) 0
  · intro k
    rw [hb0 k, hhint]; exact seedHint_getElem s (4 + 3 * k.val) (by omega) 0
  · intro k
    rw [hb1 k, hhint]; exact seedHint_getElem s (5 + 3 * k.val) (by omega) 0
  · intro k
    rw [hb2 k, hhint]; exact seedHint_getElem s (6 + 3 * k.val) (by omega) 0

/-! ## The seed stage's output expressions

`CompleteWitness` states its value fields as `Expression.eval env (seedPhase inp n).1.ry`
and friends; these lemmas identify those expressions with the wires above. -/

theorem seedPhase_out_ry (inp : Var Input Fp) (n : Nat) :
    (seedPhase inp n).1.ry = Expression.var (F := Fp) ⟨n⟩ := by
  show ((seedPhase inp).output n).ry = _
  rw [seedPhase_out]
  simp only [hint_out]

theorem seedPhase_out_hx (inp : Var Input Fp) (n : Nat) :
    (seedPhase inp n).1.hx = Expression.var (F := Fp) ⟨n + 1⟩ := by
  show ((seedPhase inp).output n).hx = _
  rw [seedPhase_out]
  simp only [hint_out]

theorem seedPhase_out_hy (inp : Var Input Fp) (n : Nat) :
    (seedPhase inp n).1.hy = Expression.var (F := Fp) ⟨n + 2⟩ := by
  show ((seedPhase inp).output n).hy = _
  rw [seedPhase_out]
  simp only [hint_out]

theorem seedPhase_out_overflow (inp : Var Input Fp) (n : Nat) :
    (seedPhase inp n).1.overflow = Expression.var (F := Fp) ⟨n + 3⟩ := by
  show ((seedPhase inp).output n).overflow = _
  rw [seedPhase_out]
  simp only [hint_out]

end StandardECDSA
