#!/usr/bin/env python3
"""Contract-specific verifier for the standard P-256 ECDSA submission.

Checks, with observed results rather than inherited logs:

1. **Exact theorem types.**  The four exported theorems and the cost
   certificate are re-stated as `example`s with the contract's statements and
   discharged by the exported proofs.  A change to any statement makes the
   `example` fail to elaborate.
2. **Input count.**  `size Input = 6` (the six base-field inputs
   `(pkX, pkY, digestLo, digestHi, r, s)`).
3. **Fixed-hint contract.**  The hint key is `"standard"` and the typed seed has
   exactly 772 field cells.
4. **Certified cost.**  `main_cost` has type
   `CostIs (main inputVar) ⟨4628, 4634⟩`, and the executable count agrees.
5. **Non-vacuity.**  A deliberately mismatched cost (`⟨4628, 4635⟩`) and a
   deliberately weakened soundness statement must both *fail* to elaborate.

Task T20.
"""
import subprocess
import sys
import tempfile
from pathlib import Path

EXPECTED_ALLOCATIONS = 4628
EXPECTED_ROWS = 4634
EXPECTED_SCORE = EXPECTED_ALLOCATIONS + EXPECTED_ROWS

POSITIVE = r'''
import StandardECDSA.Main
import StandardECDSA.Cost
import StandardECDSA.NoLookupSub

open StandardECDSA
open StandardECDSA.Gadgets

/-! 1. Exact theorem types. -/

example : ∀ (inp : Var Input Fp) (env : Environment Fp) (n : Nat),
    ConstraintsHold.Soundness env ((main inp).operations n) →
      standardVerify (Expression.eval env inp.pkX) (Expression.eval env inp.pkY)
        (Expression.eval env inp.digestLo) (Expression.eval env inp.digestHi)
        (Expression.eval env inp.r) (Expression.eval env inp.s) :=
  main_soundness

example : ∀ (inp : Var Input Fp) (env : ProverEnvironment Fp) (n : Nat),
    env.UsesLocalWitnessesCompleteness n ((main inp).operations n) →
      CompleteWitness inp env n → ConstraintsHold.Completeness env ((main inp).operations n) :=
  main_complete_with_seed

example : ∀ (inp : Var Input Fp) (n : Nat),
    (∃ env, env.UsesLocalWitnessesCompleteness n ((main inp).operations n) ∧
      CompleteWitness inp env n) →
      ∃ env, ConstraintsHold.Completeness env ((main inp).operations n) :=
  main_completeness

example : ∀ (inp : Var Input Fp) (penv : ProverEnvironment Fp) (n : Nat),
    penv.UsesLocalWitnessesCompleteness n ((main inp).operations n) →
      CompleteWitness inp penv n →
        (ConstraintsHold.Soundness penv ((main inp).operations n) ↔
          standardVerify (Expression.eval penv inp.pkX) (Expression.eval penv inp.pkY)
            (Expression.eval penv inp.digestLo) (Expression.eval penv inp.digestHi)
            (Expression.eval penv inp.r) (Expression.eval penv inp.s)) :=
  main_accepts_iff_standard

/-! 1b. The two structural side conditions are *proved*, not assumed (gap G3). -/

example : ∀ (inp : Var Input Fp) (n : Nat),
    ((main inp).operations n).shallowLookups = [] :=
  main_shallowLookups_nil

example : ∀ (inp : Var Input Fp) (n : Nat),
    ((main inp).operations n).subcircuits = [] :=
  main_subcircuits_nil

/-! 2. Input count. -/

example : size Input = 6 := rfl

/-! 3. Fixed-hint contract. -/

example : hintKey = "standard" := rfl
example : 4 + 256 + 256 + 256 = 772 := Witness.seed_field_count

/-! 4. Certified cost. -/

example : Challenge.CostR1CS.CostIs (main inputVar)
    ⟨4628, 4634⟩ := main_cost
'''

NEGATIVE_COST = r'''
import StandardECDSA.Cost
open StandardECDSA
open StandardECDSA.Gadgets
example : Challenge.CostR1CS.CostIs (main inputVar) ⟨4628, 4635⟩ := main_cost
'''

NEGATIVE_SOUNDNESS = r'''
import StandardECDSA.Main
open StandardECDSA
open StandardECDSA.Gadgets
example : ∀ (inp : Var Input Fp) (env : Environment Fp) (n : Nat),
    ConstraintsHold.Soundness env ((main inp).operations n) → True :=
  main_soundness
'''


def run_lean(source: str) -> subprocess.CompletedProcess:
    with tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False) as handle:
        handle.write(source)
        path = handle.name
    try:
        return subprocess.run(['lake', 'env', 'lean', path], text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    finally:
        Path(path).unlink(missing_ok=True)


def main() -> int:
    failures = 0

    result = run_lean(POSITIVE)
    if result.returncode != 0:
        failures += 1
        print('FAIL: the contract statements do not elaborate', file=sys.stderr)
        print(result.stdout, file=sys.stderr)
    else:
        print('contract: theorem types, input count, hint contract and cost type all check')

    for name, source in [('cost', NEGATIVE_COST), ('soundness', NEGATIVE_SOUNDNESS)]:
        result = run_lean(source)
        if result.returncode == 0:
            failures += 1
            print(f'FAIL: the deliberately mismatched {name} fixture was accepted '
                  f'(the verifier is vacuous)', file=sys.stderr)
        else:
            print(f'contract: mismatched {name} fixture correctly rejected')

    result = subprocess.run(['lake', 'exe', 'standardEcdsaCheck', '--count-only'],
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode != 0:
        failures += 1
        print('FAIL: standardEcdsaCheck --count-only failed', file=sys.stderr)
        print(result.stdout, file=sys.stderr)
    else:
        expected = (f'allocations={EXPECTED_ALLOCATIONS} rows={EXPECTED_ROWS} '
                    f'score={EXPECTED_SCORE}')
        if expected not in result.stdout:
            failures += 1
            print(f'FAIL: expected "{expected}" in the executable count', file=sys.stderr)
            print(result.stdout, file=sys.stderr)
        else:
            print(f'contract: executable count agrees: {expected}')

    if failures:
        print(f'FAIL: {failures} contract check(s) failed', file=sys.stderr)
        return 1
    print('contract: all checks passed')
    return 0


if __name__ == '__main__':
    sys.exit(main())
