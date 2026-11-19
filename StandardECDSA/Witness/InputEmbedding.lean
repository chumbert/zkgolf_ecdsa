/-
# The input embedding and the value fields of `CompleteWitness` (gap G2, step 3a)

`CompleteWitness` (`StandardECDSA/Main.lean`) states its value fields over the
*expressions* `inp.pkX`, `inp.r`, … of the circuit's input structure.  This module

* fixes the concrete input embedding — `InputEmbedding` says the six external
  inputs sit on wires `0 … 5`, which is exactly `varFromOffset Input 0`;
* proves the five value fields that follow from the embedding plus the standard
  verification predicate and the seed generator:
  `hQ` (`Q` on the curve), `hr` (`r ≠ 0`), `ht` (`n - s ≠ 0`), `hH` (`H` on the
  curve) and `hR` (`R` on the curve, the `r + n·overflow` branch).

`hR` is the interesting one: it needs the canonical overflow split
`generateSeed_overflow` to identify the circuit's `rx = r + n·overflow` with the
affine `x`-coordinate of the standard verification point `V`.

Gap G2 of `docs/m6-report.md`.
-/
import StandardECDSA.Witness.CompleteWitness
import StandardECDSA.Witness.Correctness

namespace StandardECDSA

open Circuit
open StandardECDSA.Gadgets
open StandardECDSA.Phases
open StandardECDSA.Math
open StandardECDSA.Witness

/-- The six external inputs are bound to wires `0 … 5`. -/
def InputEmbedding (inp : Var Input Fp) (env : ProverEnvironment Fp)
    (pkX pkY digestLo digestHi r s : K) : Prop :=
  Expression.eval env.toEnvironment inp.pkX = pkX ∧
    Expression.eval env.toEnvironment inp.pkY = pkY ∧
    Expression.eval env.toEnvironment inp.digestLo = digestLo ∧
    Expression.eval env.toEnvironment inp.digestHi = digestHi ∧
    Expression.eval env.toEnvironment inp.r = r ∧
    Expression.eval env.toEnvironment inp.s = s

theorem hQ_of_embedding (inp : Var Input Fp) (env : ProverEnvironment Fp)
    (pkX pkY digestLo digestHi r s : K)
    (hIn : InputEmbedding inp env pkX pkY digestLo digestHi r s)
    (hstd : standardVerify pkX pkY digestLo digestHi r s) :
    Expression.eval env.toEnvironment inp.pkY ^ 2
      = Expression.eval env.toEnvironment inp.pkX ^ 3
        + pa * Expression.eval env.toEnvironment inp.pkX + pb := by
  obtain ⟨h1, h2, -⟩ := hIn
  rw [h1, h2]
  have h := hstd.1
  unfold AffinePoint.IsOnCurve at h
  rw [show params.a = pa from rfl, show params.b = pb from rfl] at h
  rw [pow_two, show pkX ^ 3 = pkX * pkX * pkX from by ring]
  exact h

theorem hr_of_embedding (inp : Var Input Fp) (env : ProverEnvironment Fp)
    (pkX pkY digestLo digestHi r s : K)
    (hIn : InputEmbedding inp env pkX pkY digestLo digestHi r s)
    (hstd : standardVerify pkX pkY digestLo digestHi r s) :
    Expression.eval env inp.r ≠ 0 := by
  rw [hIn.2.2.2.2.1]
  intro h
  have h0 := hstd.2.1
  rw [h] at h0
  simp at h0

theorem ht_of_embedding (inp : Var Input Fp) (env : ProverEnvironment Fp)
    (pkX pkY digestLo digestHi r s : K)
    (hIn : InputEmbedding inp env pkX pkY digestLo digestHi r s)
    (hstd : standardVerify pkX pkY digestLo digestHi r s) :
    Expression.eval env (cst (Challenge.Specs.ECDSAP256.n : Fp) - inp.s) ≠ 0 := by
  rw [eval_sub, eval_cst, hIn.2.2.2.2.2]
  intro h
  have hlt : s.val < Challenge.Specs.ECDSAP256.n := hstd.2.2.2.2.1
  have hval : ((Challenge.Specs.ECDSAP256.n : Fp)).val = Challenge.Specs.ECDSAP256.n := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
    rw [show Challenge.Specs.ECDSAP256.n = n from rfl]
    exact n_lt_p
  have hsn : s = ((Challenge.Specs.ECDSAP256.n : Nat) : Fp) := (sub_eq_zero.mp h).symm
  have : s.val = Challenge.Specs.ECDSAP256.n := by rw [hsn, hval]
  omega
theorem hH_of_ulwc (inp : Var Input Fp) (s : Witness.Seed) (env : ProverEnvironment Fp)
    (n : Nat) (hhint : env.hint = seedHint s)
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hH : (s.H).IsOnCurve params) :
    Expression.eval env.toEnvironment (seedPhase inp n).1.hy ^ 2
      = Expression.eval env.toEnvironment (seedPhase inp n).1.hx ^ 3
        + pa * Expression.eval env.toEnvironment (seedPhase inp n).1.hx + pb := by
  rw [eval_seedPhase_hy inp s env n hhint hw, eval_seedPhase_hx inp s env n hhint hw]
  unfold AffinePoint.IsOnCurve at hH
  rw [show params.a = pa from rfl, show params.b = pb from rfl] at hH
  rw [pow_two, show s.hx ^ 3 = s.hx * s.hx * s.hx from by ring]
  exact hH

theorem hR_of_generateSeed (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat)
    (pkX pkY digestLo digestHi r s : K) (fam : BadFamily Grp) (hm : fam.m < 1294)
    (hhint : env.hint = seedHint (generateSeed pkX pkY digestLo digestHi r s fam hm))
    (hw : env.UsesLocalWitnessesCompleteness n ((main inp).operations n))
    (hIn : InputEmbedding inp env pkX pkY digestLo digestHi r s)
    (hstd : standardVerify pkX pkY digestLo digestHi r s) :
    Expression.eval env.toEnvironment (seedPhase inp n).1.ry ^ 2
      = Expression.eval env.toEnvironment
          (inp.r + sc nFp (seedPhase inp n).1.overflow) ^ 3
        + pa * Expression.eval env.toEnvironment
            (inp.r + sc nFp (seedPhase inp n).1.overflow) + pb := by
  set g := generateSeed pkX pkY digestLo digestHi r s fam hm with hg
  have hry := eval_seedPhase_ry inp g env n hhint hw
  have hov := eval_seedPhase_overflow inp g env n hhint hw
  rw [hry, eval_add', eval_sc', hov, hIn.2.2.2.2.1]
  have hX : r + nFp * g.overflow = stdVx pkX pkY digestLo digestHi r s := by
    set ov := overflowOf (stdVx pkX pkY digestLo digestHi r s).val r.val with hovdef
    have h3 : g.overflow = ((ov : Nat) : K) := by
      rw [hovdef]
      simp only [hg, generateSeed, stdVx]
    have h4 : r + nFp * ((ov : Nat) : K) = ((r.val + StandardECDSA.n * ov : Nat) : K) := by
      have hr : r = ((r.val : Nat) : K) := (ZMod.natCast_zmod_val r).symm
      have hn : nFp = ((StandardECDSA.n : Nat) : K) := by simp only [nFp]
      conv_lhs => rw [hr, hn]
      rw [← Nat.cast_mul, ← Nat.cast_add]
    rw [h3, h4, hovdef, ← generateSeed_overflow pkX pkY digestLo digestHi r s hstd,
      ZMod.natCast_zmod_val]
  rw [hX]
  have hon := generateSeed_R_onCurve pkX pkY digestLo digestHi r s fam hm hstd
  unfold AffinePoint.IsOnCurve at hon
  rw [show params.a = pa from rfl, show params.b = pb from rfl] at hon
  rw [pow_two, show stdVx pkX pkY digestLo digestHi r s ^ 3
      = stdVx pkX pkY digestLo digestHi r s * stdVx pkX pkY digestLo digestHi r s
        * stdVx pkX pkY digestLo digestHi r s from by ring]
  exact hon

end StandardECDSA
