#!/usr/bin/env python3
"""Fail-closed axiom audit for the standard P-256 ECDSA submission.

Runs `Tests/StandardECDSA/Axioms.lean`, which `#print axioms` every public proof
root of the development, and rejects any root that

  * is missing from the report (a root that failed to elaborate, or a root that
    was silently dropped from the audit file), or
  * depends on an axiom outside the permitted set
    `{propext, Classical.choice, Quot.sound}`.

The audit is *fail closed*: an empty report, a parse failure, or a non-zero exit
from Lean is a failure, never a pass.

Task T20.
"""
import re
import subprocess
import sys
from pathlib import Path

SOURCE = Path('Tests/StandardECDSA/Axioms.lean')
PERMITTED = {'propext', 'Quot.sound', 'Classical.choice'}

# Roots that must appear in the audit.  Kept explicit so that deleting a
# `#print axioms` line from the Lean file cannot silently shrink the audit.
REQUIRED = {
    # witness-generator causality (T18 / G2)
    'StandardECDSA.main_causal',
    'StandardECDSA.main_fixedHint_causal',
    'StandardECDSA.seedPhase_overflow_hint_causal',
    'StandardECDSA.main_ulwc_exists',
    'StandardECDSA.proverEnvironment_usesLocalWitnesses_envAgree',
    'StandardECDSA.forAll_envAgree_swap',
    'StandardECDSA.seedPhase_causal',
    'StandardECDSA.curvePhase_causal',
    'StandardECDSA.nonzeroPhase_causal',
    'StandardECDSA.bitsPhase_causal',
    'StandardECDSA.bindPhase_causal',
    'StandardECDSA.cmpPhase_causal',
    'StandardECDSA.fixedBase_causal',
    'StandardECDSA.shiftedTables_causal',
    'StandardECDSA.jointLadder_causal',
    'StandardECDSA.affAdd_causal',
    'StandardECDSA.affDouble_causal',
    'StandardECDSA.elm_causal',
    'StandardECDSA.elmTo_causal',
    'StandardECDSA.mux4W_causal',
    'StandardECDSA.muxConst4W_causal',
    'StandardECDSA.isOnCurve_causal',
    'StandardECDSA.pointEquality_causal',
    'StandardECDSA.assertLtOrderOf_causal',
    'StandardECDSA.assertLtOrderGuardedOf_causal',
    # end-to-end
    'StandardECDSA.main_soundness',
    'StandardECDSA.main_complete_with_seed',
    'StandardECDSA.main_completeness',
    'StandardECDSA.main_accepts_iff_standard',
    'StandardECDSA.main_accepts_iff_standard_of_nil',
    'StandardECDSA.main_shallowLookups_nil',
    'StandardECDSA.main_subcircuits_nil',
    'StandardECDSA.main_cost',
    # specification
    'StandardECDSA.Math.standard_iff_signaturePoint',
    'StandardECDSA.Math.x_mod_order_iff_lift',
    'StandardECDSA.Math.signature_equation_iff',
    # offset existence
    'StandardECDSA.Math.offsetCandidate_injective',
    'StandardECDSA.Math.exists_goodOffset',
    'StandardECDSA.Math.findGoodOffset_spec',
    'StandardECDSA.Math.famOf_m',
    'StandardECDSA.Math.slotEquiv',
    'StandardECDSA.Math.finProdBool',
    'StandardECDSA.Math.sumFinCongr',
    'StandardECDSA.Math.famOf_coeff_apply',
    'StandardECDSA.Math.famOf_target_apply',
    'StandardECDSA.Math.famOf_m_lt_candidates',
    'StandardECDSA.Math.exists_goodOffset_famOf',
    'StandardECDSA.Math.coeffOf_pos',
    'StandardECDSA.Math.coeffOf_lt',
    # honest-witness ladder denominators (G1-c)
    'StandardECDSA.jlAcc_eq_foldl',
    'StandardECDSA.jointLadder_ladInv',
    'StandardECDSA.sigmaZ_eq_sigma',
    'StandardECDSA.famOf_target_ladStep_false',
    'StandardECDSA.famOf_target_ladStep_true',
    'StandardECDSA.famOf_target_ladDbl_false',
    'StandardECDSA.famOf_target_ladDbl_true',
    "StandardECDSA.nsmul_eq_zsmul_int",
    'StandardECDSA.elmXu_group',
    'StandardECDSA.hj1_dx',
    'StandardECDSA.hj2_dx',
    # honest-witness final elmTo step (G1-c)
    'StandardECDSA.jointLadder_ladInv_255',
    'StandardECDSA.elmToXu_group',
    'StandardECDSA.elmTo_dx1',
    'StandardECDSA.elmTo_row5',
    'StandardECDSA.elmTo_row6',
    'StandardECDSA.jointLadder_final_rows',
    'StandardECDSA.hjf1_dx',
    'StandardECDSA.hjf2_dx',
    'StandardECDSA.hjf3_row',
    'StandardECDSA.hjf4_row',
    'StandardECDSA.jointLadder_denominators',
    # witness generation
    'StandardECDSA.Witness.generateSeed_complete',
    # group order
    'StandardECDSA.Math.n_prime',
    'StandardECDSA.Math.addOrderOf_Gpt',
    'StandardECDSA.Math.card_eq_n',
    'StandardECDSA.Math.nsmul_eq_zero',
    'StandardECDSA.Math.nsmul_injective_of_lt',
    # fixed tables
    'StandardECDSA.Math.FixedTables.mulG_toMathlib',
    'StandardECDSA.Math.FixedTables.mulG_affine_some',
    'StandardECDSA.Math.FixedTables.fixedTables_get',
    'StandardECDSA.Math.FixedTables.fixedShift_eq',
    # phase semantics
    'StandardECDSA.Phases.fixedBase_spec',
    'StandardECDSA.Phases.shiftedTables_spec',
    'StandardECDSA.Phases.jointLadder_spec',
    # phase and stage cost
    'StandardECDSA.Phases.fixedBase_cost',
    'StandardECDSA.Phases.shiftedTables_cost',
    'StandardECDSA.Phases.jointLadder_cost',
    # honest-witness row lemmas (gaps G1 / G2)
    'StandardECDSA.Phases.soundness_append_intro',
    'StandardECDSA.Phases.soundness_bind_intro',
    'StandardECDSA.Phases.muxConst4W_soundness_of_ulwc',
    'StandardECDSA.Phases.selW_soundness_of_ulwc',
    'StandardECDSA.Phases.mux4W_soundness_of_ulwc',
    'StandardECDSA.Phases.affAdd_soundness_of_ulwc',
    'StandardECDSA.Phases.elmCore_soundness_of_ulwc',
    'StandardECDSA.Phases.elm_soundness_of_ulwc',
    'StandardECDSA.Phases.fixedBaseBody_soundness_of_ulwc',
    'StandardECDSA.Phases.jointLadderBody_soundness_of_ulwc',
    'StandardECDSA.Phases.mat_soundness_of_ulwc',
    'StandardECDSA.Phases.affDouble_soundness_of_ulwc',
    'StandardECDSA.Phases.shiftedTables_soundness_of_ulwc',
    'StandardECDSA.Math.some_eq_or_neg_of_X_eq',
    'StandardECDSA.Math.X_eq_imp_bad',
    'StandardECDSA.Math.X_ne_of_avoids_sharp',
    'StandardECDSA.Math.nsmul_ne_of_slot',
    'StandardECDSA.Math.BadFamily.avoids_toAffine',
    'StandardECDSA.Math.goodOffset_avoids_affine',
    'StandardECDSA.Math.goodOffsetAffinePt_eq_some',
    'StandardECDSA.Math.nsOfOnCurve',
    'StandardECDSA.Math.nsmul_sub_of_add_eq',
    'StandardECDSA.Math.toAff_nsmul',
    'StandardECDSA.Math.X_ne_of_avoids',
    'StandardECDSA.Math.toAff_toProjective',
    'StandardECDSA.curvePhase_cost',
    'StandardECDSA.bitsPhase_cost',
    'StandardECDSA.cmpPhase_cost',
    'StandardECDSA.Phases.famOf_avoids_affine',
    'StandardECDSA.Phases.fbMux_eq',
    'StandardECDSA.Phases.famOf_target_fbWin_false',
    'StandardECDSA.Phases.famOf_target_fbWin_true',
    'StandardECDSA.Phases.fbWin_dx',
    'StandardECDSA.Phases.famOf_target_shift_false',
    'StandardECDSA.Phases.famOf_target_shift_true',
    'StandardECDSA.Phases.fbShift_dx',
    'StandardECDSA.Phases.hshy_dx',
    'StandardECDSA.Phases.toAff_zero',
    'StandardECDSA.Phases.famOf_target_sh',
    'StandardECDSA.Phases.famOf_target_sh0f',
    'StandardECDSA.Phases.famOf_target_sh0t',
    'StandardECDSA.Phases.famOf_target_sh1f',
    'StandardECDSA.Phases.famOf_target_sh1t',
    'StandardECDSA.Phases.famOf_target_sh2f',
    'StandardECDSA.Phases.famOf_target_sh2t',
    'StandardECDSA.Phases.famOf_target_sh3f',
    'StandardECDSA.Phases.famOf_target_sh3t',
    'StandardECDSA.Phases.famOf_target_sh4f',
    'StandardECDSA.Phases.famOf_target_sh4t',
    'StandardECDSA.Phases.hs1_dx',
    'StandardECDSA.Phases.hs2_dx',
    'StandardECDSA.Phases.hs3_dx',
    'StandardECDSA.Phases.hs4_dx',
    'StandardECDSA.Phases.hs5_dx',
    'StandardECDSA.Phases.zsmul_sub_of_add_eq',
    'StandardECDSA.Phases.X_eq_imp_bad_zsmul',
    'StandardECDSA.Phases.X_ne_of_avoids_zsmul',
    # witness hint bridge (gap G2)
    'StandardECDSA.Witness.seedHint_getElem',
    'StandardECDSA.Witness.seedCells_length',
    'StandardECDSA.hint_ulwc',
    'StandardECDSA.bitVec_ulwc',
    'StandardECDSA.seedPhase_ulwc',
    'StandardECDSA.bitsPhase_ulwc',
    'StandardECDSA.main_ulwc_seed_bits',
    'StandardECDSA.main_hint_cells',
    'StandardECDSA.seedPhase_out_overflow',
    'StandardECDSA.eval_seedPhase_overflow',
    'StandardECDSA.hov_of_ulwc',
    'StandardECDSA.hb_of_ulwc',
    'StandardECDSA.hbR_of_ulwc',
    'StandardECDSA.hbT_of_ulwc',
    # input embedding and value fields (gap G2)
    'StandardECDSA.InputEmbedding',
    'StandardECDSA.hQ_of_embedding',
    'StandardECDSA.hr_of_embedding',
    'StandardECDSA.ht_of_embedding',
    'StandardECDSA.hH_of_ulwc',
    'StandardECDSA.hR_of_generateSeed',
    'StandardECDSA.Phases.fixedBase_fbInv',
    'StandardECDSA.Phases.main_ulwc_fixedBase',
    'StandardECDSA.Phases.fixedBase_soundness_of_ulwc',
    'StandardECDSA.Phases.fixedBase_fbInv_of_ulwc',
    'StandardECDSA.Phases.hfb_of_ulwc',
    'StandardECDSA.Phases.hfb0_of_ulwc',
    'StandardECDSA.Phases.elmTo_soundness_of_ulwc',
    'StandardECDSA.Phases.jointLadderFinal_soundness_of_ulwc',
    'StandardECDSA.Phases.jointLadder_soundness_of_ulwc',
    'StandardECDSA.elmXu_group_of_rows',
    'StandardECDSA.elm_rows123_of_ulwc',
    'StandardECDSA.hj1_dx_of_ladInv',
    'StandardECDSA.hj2_dx_of_ladInv',
    'StandardECDSA.jointLadderBody_ladInv_step',
    'StandardECDSA.jointLadder_ladInv_of_ulwc',
}


def main() -> int:
    if not SOURCE.exists():
        print(f'FAIL: audit source {SOURCE} is missing', file=sys.stderr)
        return 1

    declared = set(re.findall(r'^#print axioms (\S+)$', SOURCE.read_text(), re.M))
    if declared != REQUIRED:
        missing = sorted(REQUIRED - declared)
        extra = sorted(declared - REQUIRED)
        print(f'FAIL: audit file does not match the required root list\n'
              f'  missing: {missing}\n  unexpected: {extra}', file=sys.stderr)
        return 1

    result = subprocess.run(
        ['lake', 'env', 'lean', str(SOURCE)],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    if result.returncode != 0:
        print(result.stdout, file=sys.stderr)
        print(f'FAIL: {SOURCE} did not elaborate (exit {result.returncode})', file=sys.stderr)
        return 1

    reports = {
        name: set(filter(None, map(str.strip, axioms.split(','))))
        for name, axioms in re.findall(
            r"'([^']+)' depends on axioms: \[([^\]]*)\]", result.stdout)
    }
    for name in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout):
        reports[name] = set()

    if set(reports) != REQUIRED:
        print(result.stdout, file=sys.stderr)
        print(f'FAIL: missing or unexpected axiom audit reports\n'
              f'  missing: {sorted(REQUIRED - set(reports))}\n'
              f'  unexpected: {sorted(set(reports) - REQUIRED)}', file=sys.stderr)
        return 1

    failures = 0
    for name in sorted(reports):
        unexpected = reports[name] - PERMITTED
        if unexpected:
            failures += 1
            print(f'FAIL: {name} depends on forbidden axioms {sorted(unexpected)}',
                  file=sys.stderr)
    if failures:
        return 1

    print(f'{SOURCE}: {len(reports)} roots passed the permitted-axiom audit '
          f'(permitted: {sorted(PERMITTED)})')
    return 0


if __name__ == '__main__':
    sys.exit(main())
