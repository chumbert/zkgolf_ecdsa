/-
# Honest-witness digest, scalar and comparator fields (task G2-a, rest)

`CompleteWitness`'s remaining non-group fields are

* `hd0`..`hd3` — the bit vectors the bits stage allocates recompose to the four
  input limbs (`digestLo`, `digestHi`, `r`, `n - s`);
* `hle`, `hle'` — the comparator preconditions `r ≤ n - 1`, `n - s ≤ n - 1`;
* `hleg` — the overflow branch `overflow = 1 → r ≤ p - n - 1`.

Each `hd*` is a `linComb` evaluation (`eval_linComb`), a per-bit identification
with the seed's own bit vectors (`main_hint_cells` + `seedCells_getD_*`), and
then a *value* comparison: `val_leSum` / `val_leSum'` turn the field sum into the
natural little-endian sum, `ScalarFacts` identifies that sum with the limb, and
`ZMod.val_injective` closes the field equality.

`hle`/`hle'` rewrite the reversed prefix value as `leNat` (`prefVal_rev`), read it
as the `aNatOf` of the circuit's own bit wires (`leNat_val_eq_aNatOf`), and bound
it by `n - 1` from `ScalarFacts.rBits_val` / `tBits_val`.  `hleg` additionally
uses the canonical overflow split `generateSeed_overflow`.

No new axioms, no `native_decide`, no `sorry`.
-/
import StandardECDSA.Witness.CompleteWitness
import StandardECDSA.Witness.Correctness
import StandardECDSA.Math.ScalarEncoding

namespace StandardECDSA

open Circuit
open StandardECDSA.Gadgets
open StandardECDSA.Phases
open StandardECDSA.Math
open StandardECDSA.Witness

/-! ## The per-bit identifications -/

/-- The low digest bits of the bits stage are the seed's digest bits. -/
theorem ebBits_of_main (inp : Var Input Fp) (sd : Witness.Seed) (env : ProverEnvironment Fp)
    (n : Nat) (hhint : env.hint = Witness.seedHint sd)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    ∀ i : Fin 128,
      Expression.eval env.toEnvironment
        ((bitsPhase (off3 inp n)).1.eb.getD (0 + i.val) (cst 0))
        = sd.digestBits (Fin.castLE (by norm_num) i) := by
  intro i
  rw [getD_eq_get (v := (bitsPhase (off3 inp n)).1.eb) (by omega : 0 + i.val < 256)]
  simp only [Nat.zero_add]
  rw [bitsPhase_out_eb, eval_var]
  rw [((main_hint_cells inp sd env n hhint hw).2.2.2.2.1 ⟨i.val, by omega⟩),
    Witness.seedCells_getD_digest]
  rfl

/-- The high digest bits of the bits stage are the seed's digest bits. -/
theorem ebBitsHi_of_main (inp : Var Input Fp) (sd : Witness.Seed) (env : ProverEnvironment Fp)
    (n : Nat) (hhint : env.hint = Witness.seedHint sd)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    ∀ i : Fin 128,
      Expression.eval env.toEnvironment
        ((bitsPhase (off3 inp n)).1.eb.getD (128 + i.val) (cst 0))
        = sd.digestBits (Fin.natAdd 128 i) := by
  intro i
  rw [getD_eq_get (v := (bitsPhase (off3 inp n)).1.eb) (by omega : 128 + i.val < 256),
    bitsPhase_out_eb, eval_var]
  rw [((main_hint_cells inp sd env n hhint hw).2.2.2.2.1 ⟨128 + i.val, by omega⟩),
    Witness.seedCells_getD_digest]
  rfl

/-- The `r` bits of the bits stage are the seed's `r` bits. -/
theorem rbBits_of_main (inp : Var Input Fp) (sd : Witness.Seed) (env : ProverEnvironment Fp)
    (n : Nat) (hhint : env.hint = Witness.seedHint sd)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    ∀ i : Fin 256,
      Expression.eval env.toEnvironment
        ((bitsPhase (off3 inp n)).1.rb.getD (0 + i.val) (cst 0)) = sd.rBits i := by
  intro i
  rw [getD_eq_get (v := (bitsPhase (off3 inp n)).1.rb) (by omega : 0 + i.val < 256)]
  simp only [Nat.zero_add]
  rw [bitsPhase_out_rb, eval_var]
  rw [((main_hint_cells inp sd env n hhint hw).2.2.2.2.2.1 ⟨i.val, by omega⟩),
    Witness.seedCells_getD_r]

/-- The `t` bits of the bits stage are the seed's `t` bits. -/
theorem sbBits_of_main (inp : Var Input Fp) (sd : Witness.Seed) (env : ProverEnvironment Fp)
    (n : Nat) (hhint : env.hint = Witness.seedHint sd)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    ∀ i : Fin 256,
      Expression.eval env.toEnvironment
        ((bitsPhase (off3 inp n)).1.sb.getD (0 + i.val) (cst 0)) = sd.tBits i := by
  intro i
  rw [getD_eq_get (v := (bitsPhase (off3 inp n)).1.sb) (by omega : 0 + i.val < 256)]
  simp only [Nat.zero_add]
  rw [bitsPhase_out_sb, eval_var]
  rw [((main_hint_cells inp sd env n hhint hw).2.2.2.2.2.2 ⟨i.val, by omega⟩),
    Witness.seedCells_getD_t]

/-- The `r`-bit wires of the bits stage are the seed's `r` bits. -/
theorem rbGet_of_main (inp : Var Input Fp) (sd : Witness.Seed) (env : ProverEnvironment Fp)
    (n : Nat) (hhint : env.hint = Witness.seedHint sd)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    ∀ k : Fin 256,
      Expression.eval env.toEnvironment ((bitsPhase (off3 inp n)).1.rb.get k) = sd.rBits k := by
  intro k
  have h := rbBits_of_main inp sd env n hhint hw k
  simp only [Nat.zero_add] at h
  rw [getD_eq_get (v := (bitsPhase (off3 inp n)).1.rb) k.isLt] at h
  exact h

/-- The `t`-bit wires of the bits stage are the seed's `t` bits. -/
theorem sbGet_of_main (inp : Var Input Fp) (sd : Witness.Seed) (env : ProverEnvironment Fp)
    (n : Nat) (hhint : env.hint = Witness.seedHint sd)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n)) :
    ∀ k : Fin 256,
      Expression.eval env.toEnvironment ((bitsPhase (off3 inp n)).1.sb.get k) = sd.tBits k := by
  intro k
  have h := sbBits_of_main inp sd env n hhint hw k
  simp only [Nat.zero_add] at h
  rw [getD_eq_get (v := (bitsPhase (off3 inp n)).1.sb) k.isLt] at h
  exact h

/-! ## The digest-limb arithmetic -/

/-- The low 128 bits of `E = lo + 2^128 * hi` are `lo`, for a 128-bit `lo`. -/
theorem digestLo_mod (lo hi : K) (E : Nat) (hE : E = digestOf lo hi)
    (hlo : lo.val < 2 ^ 128) : E % 2 ^ 128 = lo.val := by
  rw [hE]
  show (lo.val + 2 ^ 128 * hi.val) % 2 ^ 128 = lo.val
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]

/-- The high 128 bits of `E = lo + 2^128 * hi` are `hi`, for a 128-bit `lo`. -/
theorem digestHi_div (lo hi : K) (E : Nat) (hE : E = digestOf lo hi)
    (hlo : lo.val < 2 ^ 128) : E / 2 ^ 128 = hi.val := by
  rw [hE]
  show (lo.val + 2 ^ 128 * hi.val) / 2 ^ 128 = hi.val
  rw [Nat.mul_comm (2 ^ 128) hi.val,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 2 ^ 128),
    Nat.div_eq_of_lt hlo, Nat.zero_add]

/-! ## `hd0` and `hd1` -/

/-- `CompleteWitness.hd0`: the low digest bits recompose to `inp.digestLo`. -/
theorem hd0_of_ulwc (inp : Var Input Fp) (sd : Witness.Seed) (env : ProverEnvironment Fp)
    (n : Nat) (E r t : Nat) (digestLo digestHi : K)
    (hhint : env.hint = Witness.seedHint sd)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hsc : ScalarFacts sd E r t)
    (hIn : Expression.eval env.toEnvironment inp.digestLo = digestLo)
    (hE : E = digestOf digestLo digestHi) (hlo : digestLo.val < 2 ^ 128) :
    Expression.eval env (linComb (bitsPhase (off3 inp n)).1.eb 0 128)
      = Expression.eval env inp.digestLo := by
  rw [eval_linComb, hIn]
  have hval := ebBits_of_main inp sd env n hhint hw
  have hcongr : leSum (fun i : Fin 128 => Expression.eval env.toEnvironment
      ((bitsPhase (off3 inp n)).1.eb.getD (0 + i.val) (cst 0)))
      = leSum (fun i : Fin 128 => (sd.digestBits (Fin.castLE (by norm_num) i) : K)) := by
    congr 1
    funext i
    rw [hval i]
  rw [hcongr]
  have hbits : ∀ i : Fin 128,
      (sd.digestBits (Fin.castLE (by norm_num) i) : K) = 0 ∨
        (sd.digestBits (Fin.castLE (by norm_num) i) : K) = 1 :=
    fun i => hsc.digestBits_bool _
  have hv := val_leSum (fun i : Fin 128 => (sd.digestBits (Fin.castLE (by norm_num) i) : K))
    hbits two_pow_128_le_p
  have hval2 : (leSum (fun i : Fin 128 =>
      (sd.digestBits (Fin.castLE (by norm_num) i) : K))).val = digestLo.val := by
    rw [hv, hsc.digestLo_val, digestLo_mod digestLo digestHi E hE hlo]
  exact ZMod.val_injective p hval2

/-- `CompleteWitness.hd1`: the high digest bits recompose to `inp.digestHi`. -/
theorem hd1_of_ulwc (inp : Var Input Fp) (sd : Witness.Seed) (env : ProverEnvironment Fp)
    (n : Nat) (E r t : Nat) (digestLo digestHi : K)
    (hhint : env.hint = Witness.seedHint sd)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hsc : ScalarFacts sd E r t)
    (hIn : Expression.eval env.toEnvironment inp.digestHi = digestHi)
    (hE : E = digestOf digestLo digestHi) (hlo : digestLo.val < 2 ^ 128)
    (_hhi : digestHi.val < 2 ^ 128) :
    Expression.eval env (linComb (bitsPhase (off3 inp n)).1.eb 128 128)
      = Expression.eval env inp.digestHi := by
  rw [eval_linComb, hIn]
  have hval := ebBitsHi_of_main inp sd env n hhint hw
  have hcongr : leSum (fun i : Fin 128 => Expression.eval env.toEnvironment
      ((bitsPhase (off3 inp n)).1.eb.getD (128 + i.val) (cst 0)))
      = leSum (fun i : Fin 128 => (sd.digestBits (Fin.natAdd 128 i) : K)) := by
    congr 1
    funext i
    rw [hval i]
  rw [hcongr]
  have hbits : ∀ i : Fin 128,
      (sd.digestBits (Fin.natAdd 128 i) : K) = 0 ∨
        (sd.digestBits (Fin.natAdd 128 i) : K) = 1 :=
    fun i => hsc.digestBits_bool _
  have hv := val_leSum (fun i : Fin 128 => (sd.digestBits (Fin.natAdd 128 i) : K))
    hbits two_pow_128_le_p
  have hval2 : (leSum (fun i : Fin 128 =>
      (sd.digestBits (Fin.natAdd 128 i) : K))).val = digestHi.val := by
    rw [hv, hsc.digestHi_val, digestHi_div digestLo digestHi E hE hlo]
  exact ZMod.val_injective p hval2

/-! ## `hd2` and `hd3` -/

/-- `CompleteWitness.hd2`: the `r` bits recompose to `inp.r`. -/
theorem hd2_of_ulwc (inp : Var Input Fp) (sd : Witness.Seed) (env : ProverEnvironment Fp)
    (n : Nat) (E r t : Nat)
    (hhint : env.hint = Witness.seedHint sd)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hsc : ScalarFacts sd E r t)
    (hIn : Expression.eval env.toEnvironment inp.r = (r : K))
    (hrn : r < StandardECDSA.n) :
    Expression.eval env (linComb (bitsPhase (off3 inp n)).1.rb 0 256)
      = Expression.eval env inp.r := by
  rw [eval_linComb, hIn]
  have hval := rbBits_of_main inp sd env n hhint hw
  have hcongr : leSum (fun i : Fin 256 => Expression.eval env.toEnvironment
      ((bitsPhase (off3 inp n)).1.rb.getD (0 + i.val) (cst 0)))
      = leSum (fun i : Fin 256 => (sd.rBits i : K)) := by
    congr 1
    funext i
    rw [hval i]
  rw [hcongr]
  have hbits : ∀ i : Fin 256, (sd.rBits i : K) = 0 ∨ (sd.rBits i : K) = 1 :=
    fun i => hsc.rBits_bool _
  have hlt : leNat (fun i : Fin 256 => ((sd.rBits i : K)).val) < p := by
    rw [hsc.rBits_val]
    exact lt_trans hrn n_lt_p
  have hv := val_leSum' (fun i : Fin 256 => (sd.rBits i : K)) hbits hlt
  have hval2 : (leSum (fun i : Fin 256 => (sd.rBits i : K))).val = ((r : K)).val := by
    rw [hv, hsc.rBits_val]
    exact (ZMod.val_cast_of_lt (lt_trans hrn n_lt_p)).symm
  exact ZMod.val_injective p hval2

/-- `CompleteWitness.hd3`: the `t` bits recompose to `n - inp.s`. -/
theorem hd3_of_ulwc (inp : Var Input Fp) (sd : Witness.Seed) (env : ProverEnvironment Fp)
    (n : Nat) (E r t : Nat) (s : K)
    (hhint : env.hint = Witness.seedHint sd)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hsc : ScalarFacts sd E r t)
    (hIn : Expression.eval env.toEnvironment inp.s = s)
    (hsn : s.val < Challenge.Specs.ECDSAP256.n)
    (ht : t = StandardECDSA.n - s.val) :
    Expression.eval env (linComb (bitsPhase (off3 inp n)).1.sb 0 256)
      = Expression.eval env (cst (Challenge.Specs.ECDSAP256.n : Fp) - inp.s) := by
  rw [eval_linComb]
  have hval := sbBits_of_main inp sd env n hhint hw
  have hcongr : leSum (fun i : Fin 256 => Expression.eval env.toEnvironment
      ((bitsPhase (off3 inp n)).1.sb.getD (0 + i.val) (cst 0)))
      = leSum (fun i : Fin 256 => (sd.tBits i : K)) := by
    congr 1
    funext i
    rw [hval i]
  rw [hcongr]
  have hbits : ∀ i : Fin 256, (sd.tBits i : K) = 0 ∨ (sd.tBits i : K) = 1 :=
    fun i => hsc.tBits_bool _
  have hlt : leNat (fun i : Fin 256 => ((sd.tBits i : K)).val) < p := by
    rw [hsc.tBits_val, ht]
    exact lt_of_le_of_lt (Nat.sub_le _ _) n_lt_p
  have hv := val_leSum' (fun i : Fin 256 => (sd.tBits i : K)) hbits hlt
  have hval2 : (leSum (fun i : Fin 256 => (sd.tBits i : K))).val
      = Challenge.Specs.ECDSAP256.n - s.val := by
    rw [hv, hsc.tBits_val, ht]
  have hrhs : (Expression.eval env (cst (Challenge.Specs.ECDSAP256.n : Fp) - inp.s)).val
      = Challenge.Specs.ECDSAP256.n - s.val := by
    rw [eval_sub, eval_cst, hIn, val_nFp_sub _ hsn]
  exact ZMod.val_injective p (hval2.trans hrhs.symm)

/-! ## The comparator preconditions -/

/-- The reversed prefix value of the circuit's `r`-bit wires is `r`. -/
theorem prefVal_rb_of_main (inp : Var Input Fp) (sd : Witness.Seed)
    (env : ProverEnvironment Fp) (n : Nat) (E r t : Nat)
    (hhint : env.hint = Witness.seedHint sd)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hsc : ScalarFacts sd E r t) :
    prefVal (fun j => aNatOf (fun k => Expression.eval env.toEnvironment
      ((bitsPhase (off3 inp n)).1.rb.getD k (cst 0))) (255 - j)) 256 = r := by
  have hb : ∀ k : Fin 256, Expression.eval env.toEnvironment
      ((bitsPhase (off3 inp n)).1.rb.get k) = 0 ∨
      Expression.eval env.toEnvironment ((bitsPhase (off3 inp n)).1.rb.get k) = 1 := by
    intro k
    rw [rbGet_of_main inp sd env n hhint hw k]
    exact hsc.rBits_bool k
  rw [prefVal_rev_nat (fun k => aNatOf (fun k => Expression.eval env.toEnvironment
    ((bitsPhase (off3 inp n)).1.rb.getD k (cst 0))) k)]
  rw [← leNat_val_eq_aNatOf env ((bitsPhase (off3 inp n)).1.rb) hb]
  rw [leNat_congr (fun i => by rw [rbGet_of_main inp sd env n hhint hw i]), hsc.rBits_val]

/-- The reversed prefix value of the circuit's `t`-bit wires is `t`. -/
theorem prefVal_sb_of_main (inp : Var Input Fp) (sd : Witness.Seed)
    (env : ProverEnvironment Fp) (n : Nat) (E r t : Nat)
    (hhint : env.hint = Witness.seedHint sd)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hsc : ScalarFacts sd E r t) :
    prefVal (fun j => aNatOf (fun k => Expression.eval env.toEnvironment
      ((bitsPhase (off3 inp n)).1.sb.getD k (cst 0))) (255 - j)) 256 = t := by
  have hb : ∀ k : Fin 256, Expression.eval env.toEnvironment
      ((bitsPhase (off3 inp n)).1.sb.get k) = 0 ∨
      Expression.eval env.toEnvironment ((bitsPhase (off3 inp n)).1.sb.get k) = 1 := by
    intro k
    rw [sbGet_of_main inp sd env n hhint hw k]
    exact hsc.tBits_bool k
  rw [prefVal_rev_nat (fun k => aNatOf (fun k => Expression.eval env.toEnvironment
    ((bitsPhase (off3 inp n)).1.sb.getD k (cst 0))) k)]
  rw [← leNat_val_eq_aNatOf env ((bitsPhase (off3 inp n)).1.sb) hb]
  rw [leNat_congr (fun i => by rw [sbGet_of_main inp sd env n hhint hw i]), hsc.tBits_val]

/-- `CompleteWitness.hle`: the `r` bits are below the group order. -/
theorem hle_of_ulwc (inp : Var Input Fp) (sd : Witness.Seed) (env : ProverEnvironment Fp)
    (n : Nat) (E r t : Nat)
    (hhint : env.hint = Witness.seedHint sd)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hsc : ScalarFacts sd E r t) (hrn : r < StandardECDSA.n) :
    prefVal (fun j => aNatOf (fun k => Expression.eval env.toEnvironment
      ((bitsPhase (off3 inp n)).1.rb.getD k (cst 0))) (255 - j)) 256 ≤ nSubOne := by
  rw [prefVal_rb_of_main inp sd env n E r t hhint hw hsc]
  have hrn' : r < Challenge.Specs.ECDSAP256.n := hrn
  unfold nSubOne
  omega

/-- `CompleteWitness.hle'`: the `t` bits are below the group order. -/
theorem hle'_of_ulwc (inp : Var Input Fp) (sd : Witness.Seed) (env : ProverEnvironment Fp)
    (n : Nat) (E r t : Nat)
    (hhint : env.hint = Witness.seedHint sd)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hsc : ScalarFacts sd E r t) (htn : t < StandardECDSA.n) :
    prefVal (fun j => aNatOf (fun k => Expression.eval env.toEnvironment
      ((bitsPhase (off3 inp n)).1.sb.getD k (cst 0))) (255 - j)) 256 ≤ nSubOne := by
  rw [prefVal_sb_of_main inp sd env n E r t hhint hw hsc]
  have htn' : t < Challenge.Specs.ECDSAP256.n := htn
  unfold nSubOne
  omega

/-- The overflow branch bound: `overflow = 1` forces `r ≤ p - n - 1`. -/
theorem overflow_bound (rx r : Nat) (hrx : rx = r + StandardECDSA.n * overflowOf rx r)
    (hrxlt : rx < p) (h : overflowOf rx r = 1) : r ≤ pSubNSubOne := by
  have hb : overflowOf rx r ≤ 1 := by
    unfold overflowOf
    split <;> omega
  have h1 : rx = r + StandardECDSA.n := by rw [hrx, h]; ring
  have hn := n_lt_p
  show r ≤ StandardECDSA.p - StandardECDSA.n - 1
  omega

/-- `CompleteWitness.hleg`: in the overflow branch the `r` bits are below
`p - n - 1`. -/
theorem hleg_of_ulwc (inp : Var Input Fp) (sd : Witness.Seed) (env : ProverEnvironment Fp)
    (n : Nat) (E r t : Nat) (rx : Nat)
    (hhint : env.hint = Witness.seedHint sd)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hsc : ScalarFacts sd E r t)
    (hov : Expression.eval env.toEnvironment (seedPhase inp n).1.overflow
      = ((overflowOf rx r : Nat) : K))
    (hrx : rx = r + StandardECDSA.n * overflowOf rx r) (hrxlt : rx < p) :
    Expression.eval env.toEnvironment (seedPhase inp n).1.overflow = 1 →
      prefVal (fun j => aNatOf (fun k => Expression.eval env.toEnvironment
        ((bitsPhase (off3 inp n)).1.rb.getD k (cst 0))) (255 - j)) 256 ≤ pSubNSubOne := by
  intro hov1
  have hovn : overflowOf rx r = 1 := by
    have h1 : ((overflowOf rx r : Nat) : K) = ((1 : Nat) : K) := by
      rw [← hov]; exact hov1
    have h2 := congrArg ZMod.val h1
    have hb : overflowOf rx r ≤ 1 := by
      unfold overflowOf
      split <;> omega
    have hp1 : 1 < p := by norm_num
    rw [ZMod.val_natCast, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by omega : overflowOf rx r < p),
      Nat.mod_eq_of_lt hp1] at h2
    exact h2
  rw [prefVal_rb_of_main inp sd env n E r t hhint hw hsc]
  exact overflow_bound rx r hrx hrxlt hovn

end StandardECDSA
