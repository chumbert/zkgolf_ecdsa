/-
# Axiom audit for the standard P-256 ECDSA submission

Every public proof root of the standard-ECDSA development is audited here.  The
fail-closed checker `scripts/check_standard_ecdsa_axioms.py` runs this file and
rejects any root that depends on an axiom outside

    { propext, Classical.choice, Quot.sound }.

The roots are grouped as in the plan's T20 acceptance list:

* **end-to-end** — the four exported theorems of `StandardECDSA/Main.lean` plus
  the exact cost certificate;
* **specification** — the standard-ECDSA specification and its equivalence with
  the signature-point predicate;
* **offset existence** — the 1,040-candidate / 1,039-slot counting argument;
* **witness generation** — the honest seed generator;
* **group order** — the P-256 group-order certificates;
* **fixed tables** — the 128×4 fixed-base table and the shift point;
* **phase semantics** — the three arithmetic phases' group-level specs;
* **phase cost** — the per-phase and per-stage allocation/row certificates.

Task T20.
-/

import StandardECDSA.Main
import StandardECDSA.Cost
import StandardECDSA.NoLookupSub
import StandardECDSA.Math.SignatureEquation
import StandardECDSA.Math.OffsetCandidates
import StandardECDSA.Math.OffsetFamily
import StandardECDSA.Witness.Correctness
import StandardECDSA.Math.GroupOrder
import StandardECDSA.Math.FixedTables
import StandardECDSA.Phases.FixedBaseSemantics
import StandardECDSA.Phases.TableSemantics
import StandardECDSA.Phases.LadderSemantics
import StandardECDSA.Phases.Cost
import StandardECDSA.Phases.HonestWitness
import StandardECDSA.Math.DenominatorBridge
import StandardECDSA.WitgenCausality
import StandardECDSA.Phases.HonestDenominators
import StandardECDSA.Phases.HonestShifted
import StandardECDSA.HonestLadder

/-! ## End-to-end -/

#print axioms StandardECDSA.main_soundness
#print axioms StandardECDSA.main_complete_with_seed
#print axioms StandardECDSA.main_completeness
#print axioms StandardECDSA.main_accepts_iff_standard
#print axioms StandardECDSA.main_accepts_iff_standard_of_nil
#print axioms StandardECDSA.main_shallowLookups_nil
#print axioms StandardECDSA.main_subcircuits_nil
#print axioms StandardECDSA.main_cost

/-! ## Specification -/

#print axioms StandardECDSA.Math.standard_iff_signaturePoint
#print axioms StandardECDSA.Math.x_mod_order_iff_lift
#print axioms StandardECDSA.Math.signature_equation_iff

/-! ## Offset existence -/

#print axioms StandardECDSA.Math.offsetCandidate_injective
#print axioms StandardECDSA.Math.exists_goodOffset
#print axioms StandardECDSA.Math.findGoodOffset_spec
#print axioms StandardECDSA.Math.famOf_m
#print axioms StandardECDSA.Math.slotEquiv
#print axioms StandardECDSA.Math.finProdBool
#print axioms StandardECDSA.Math.sumFinCongr
#print axioms StandardECDSA.Math.famOf_coeff_apply
#print axioms StandardECDSA.Math.famOf_target_apply
#print axioms StandardECDSA.Math.famOf_m_lt_candidates
#print axioms StandardECDSA.Math.exists_goodOffset_famOf
#print axioms StandardECDSA.Math.coeffOf_pos
#print axioms StandardECDSA.Math.coeffOf_lt

/-! ## Witness generation -/

#print axioms StandardECDSA.Witness.generateSeed_complete

/-! ## Group order -/

#print axioms StandardECDSA.Math.n_prime
#print axioms StandardECDSA.Math.addOrderOf_Gpt
#print axioms StandardECDSA.Math.card_eq_n
#print axioms StandardECDSA.Math.nsmul_eq_zero
#print axioms StandardECDSA.Math.nsmul_injective_of_lt

/-! ## Fixed tables -/

#print axioms StandardECDSA.Math.FixedTables.mulG_toMathlib
#print axioms StandardECDSA.Math.FixedTables.mulG_affine_some
#print axioms StandardECDSA.Math.FixedTables.fixedTables_get
#print axioms StandardECDSA.Math.FixedTables.fixedShift_eq

/-! ## Phase semantics -/

#print axioms StandardECDSA.Phases.fixedBase_spec
#print axioms StandardECDSA.Phases.shiftedTables_spec
#print axioms StandardECDSA.Phases.jointLadder_spec

/-! ## Phase and stage cost -/

#print axioms StandardECDSA.Phases.fixedBase_cost
#print axioms StandardECDSA.Phases.shiftedTables_cost
#print axioms StandardECDSA.Phases.jointLadder_cost

/-! ## Honest-witness row lemmas (gaps G1 / G2) -/

#print axioms StandardECDSA.Phases.soundness_append_intro
#print axioms StandardECDSA.Phases.soundness_bind_intro
#print axioms StandardECDSA.Phases.muxConst4W_soundness_of_ulwc
#print axioms StandardECDSA.Phases.selW_soundness_of_ulwc
#print axioms StandardECDSA.Phases.mux4W_soundness_of_ulwc
#print axioms StandardECDSA.Phases.affAdd_soundness_of_ulwc
#print axioms StandardECDSA.Phases.elmCore_soundness_of_ulwc
#print axioms StandardECDSA.Phases.elm_soundness_of_ulwc
#print axioms StandardECDSA.Phases.fixedBaseBody_soundness_of_ulwc
#print axioms StandardECDSA.Phases.jointLadderBody_soundness_of_ulwc
#print axioms StandardECDSA.Phases.mat_soundness_of_ulwc
#print axioms StandardECDSA.Phases.affDouble_soundness_of_ulwc
#print axioms StandardECDSA.Phases.shiftedTables_soundness_of_ulwc
#print axioms StandardECDSA.Math.some_eq_or_neg_of_X_eq
#print axioms StandardECDSA.Math.X_eq_imp_bad
#print axioms StandardECDSA.Math.X_ne_of_avoids
#print axioms StandardECDSA.Math.nsmul_ne_of_slot
#print axioms StandardECDSA.Math.BadFamily.avoids_toAffine
#print axioms StandardECDSA.Math.goodOffset_avoids_affine
#print axioms StandardECDSA.Math.goodOffsetAffinePt_eq_some
#print axioms StandardECDSA.Math.nsOfOnCurve
#print axioms StandardECDSA.Math.nsmul_sub_of_add_eq
#print axioms StandardECDSA.Math.toAff_nsmul
#print axioms StandardECDSA.Math.X_ne_of_avoids_sharp
#print axioms StandardECDSA.Math.toAff_toProjective
#print axioms StandardECDSA.curvePhase_cost
#print axioms StandardECDSA.bitsPhase_cost
#print axioms StandardECDSA.cmpPhase_cost
#print axioms StandardECDSA.Phases.famOf_avoids_affine
#print axioms StandardECDSA.Phases.fbMux_eq
#print axioms StandardECDSA.Phases.famOf_target_fbWin_false
#print axioms StandardECDSA.Phases.famOf_target_fbWin_true
#print axioms StandardECDSA.Phases.fbWin_dx
#print axioms StandardECDSA.Phases.famOf_target_shift_false
#print axioms StandardECDSA.Phases.famOf_target_shift_true
#print axioms StandardECDSA.Phases.fbShift_dx
#print axioms StandardECDSA.Phases.hshy_dx
#print axioms StandardECDSA.Phases.toAff_zero
#print axioms StandardECDSA.Phases.famOf_target_sh
#print axioms StandardECDSA.Phases.famOf_target_sh0f
#print axioms StandardECDSA.Phases.famOf_target_sh0t
#print axioms StandardECDSA.Phases.famOf_target_sh1f
#print axioms StandardECDSA.Phases.famOf_target_sh1t
#print axioms StandardECDSA.Phases.famOf_target_sh2f
#print axioms StandardECDSA.Phases.famOf_target_sh2t
#print axioms StandardECDSA.Phases.famOf_target_sh3f
#print axioms StandardECDSA.Phases.famOf_target_sh3t
#print axioms StandardECDSA.Phases.famOf_target_sh4f
#print axioms StandardECDSA.Phases.famOf_target_sh4t
#print axioms StandardECDSA.Phases.hs1_dx
#print axioms StandardECDSA.Phases.hs2_dx
#print axioms StandardECDSA.Phases.hs3_dx
#print axioms StandardECDSA.Phases.hs4_dx
#print axioms StandardECDSA.Phases.hs5_dx
#print axioms StandardECDSA.Phases.zsmul_sub_of_add_eq
#print axioms StandardECDSA.Phases.X_eq_imp_bad_zsmul
#print axioms StandardECDSA.Phases.X_ne_of_avoids_zsmul

/-! ## Honest-witness ladder denominators (G1-c) -/

#print axioms StandardECDSA.jlAcc_eq_foldl
#print axioms StandardECDSA.jointLadder_ladInv
#print axioms StandardECDSA.sigmaZ_eq_sigma
#print axioms StandardECDSA.famOf_target_ladStep_false
#print axioms StandardECDSA.famOf_target_ladStep_true
#print axioms StandardECDSA.famOf_target_ladDbl_false
#print axioms StandardECDSA.famOf_target_ladDbl_true
#print axioms StandardECDSA.nsmul_eq_zsmul_int
#print axioms StandardECDSA.elmXu_group
#print axioms StandardECDSA.hj1_dx
#print axioms StandardECDSA.hj2_dx

/-! ## Honest-witness final `elmTo` step (G1-c) -/

#print axioms StandardECDSA.jointLadder_ladInv_255
#print axioms StandardECDSA.elmToXu_group
#print axioms StandardECDSA.elmTo_dx1
#print axioms StandardECDSA.elmTo_row5
#print axioms StandardECDSA.elmTo_row6
#print axioms StandardECDSA.jointLadder_final_rows
#print axioms StandardECDSA.hjf1_dx
#print axioms StandardECDSA.hjf2_dx
#print axioms StandardECDSA.hjf3_row
#print axioms StandardECDSA.hjf4_row
#print axioms StandardECDSA.jointLadder_denominators

/-! ## Witness-generator causality (T18 / G2) -/

#print axioms StandardECDSA.main_causal
#print axioms StandardECDSA.main_fixedHint_causal
#print axioms StandardECDSA.seedPhase_overflow_hint_causal
#print axioms StandardECDSA.main_ulwc_exists
#print axioms StandardECDSA.proverEnvironment_usesLocalWitnesses_envAgree
#print axioms StandardECDSA.forAll_envAgree_swap
#print axioms StandardECDSA.seedPhase_causal
#print axioms StandardECDSA.curvePhase_causal
#print axioms StandardECDSA.nonzeroPhase_causal
#print axioms StandardECDSA.bitsPhase_causal
#print axioms StandardECDSA.bindPhase_causal
#print axioms StandardECDSA.cmpPhase_causal
#print axioms StandardECDSA.fixedBase_causal
#print axioms StandardECDSA.shiftedTables_causal
#print axioms StandardECDSA.jointLadder_causal
#print axioms StandardECDSA.affAdd_causal
#print axioms StandardECDSA.affDouble_causal
#print axioms StandardECDSA.elm_causal
#print axioms StandardECDSA.elmTo_causal
#print axioms StandardECDSA.mux4W_causal
#print axioms StandardECDSA.muxConst4W_causal
#print axioms StandardECDSA.isOnCurve_causal
#print axioms StandardECDSA.pointEquality_causal
#print axioms StandardECDSA.assertLtOrderOf_causal
#print axioms StandardECDSA.assertLtOrderGuardedOf_causal
