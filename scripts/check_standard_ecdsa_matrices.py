#!/usr/bin/env python3
"""Independent validation of the exported standard-ECDSA R1CS matrices.

Reads the directory written by

    lake exe standardEcdsaCheck --export=<dir>

which contains

  * `rows.txt`    — one line per assertion, `A;B;C` where each of `A`, `B`, `C`
                    is a sparse affine form `i:c,j:c,...|k` (variable index and
                    coefficient pairs, then the constant term);
  * `witness.txt` — the full wire assignment, one field element per line;
  * `meta.txt`    — input count, allocation/row counts and the six input values.

and checks, without trusting Lean:

  1. the row count and wire count match the certified cost (4,634 / 4,634);
  2. every row is satisfied: `A·z · B·z = C·z` in `F_p`;
  3. the six external inputs are bound to wires `0 … 5` and equal the declared
     input values;
  4. mutating any single auxiliary wire breaks at least one row (so the
     assignment is not vacuously satisfying).

Matrix export is *tested tooling*: this script validates the exported data, it
does not prove the exporter correct.

Task T20.
"""
import sys
from pathlib import Path

P = 2**256 - 2**224 + 2**192 + 2**96 - 1
EXPECTED_ROWS = 4634
EXPECTED_WIRES = 4634
INPUT_COUNT = 6


def parse_lf(text):
    """Parse `i:c,j:c,...|k` into `(pairs, const)`."""
    coeffs, const = text.split('|')
    pairs = []
    if coeffs:
        for term in coeffs.split(','):
            index, value = term.split(':')
            pairs.append((int(index), int(value)))
    return pairs, int(const)


def eval_lf(form, z):
    pairs, const = form
    acc = const
    for index, value in pairs:
        acc += value * z[index]
    return acc % P


def main(argv):
    if len(argv) != 2:
        print('usage: check_standard_ecdsa_matrices.py <export-directory>', file=sys.stderr)
        return 2
    directory = Path(argv[1])
    for name in ('rows.txt', 'witness.txt', 'meta.txt'):
        if not (directory / name).exists():
            print(f'FAIL: {directory / name} is missing', file=sys.stderr)
            return 1

    meta = dict(
        line.split('=', 1)
        for line in (directory / 'meta.txt').read_text().splitlines()
        if '=' in line
    )
    raw_rows = [line for line in (directory / 'rows.txt').read_text().splitlines() if line]
    z = [int(line) for line in (directory / 'witness.txt').read_text().splitlines() if line]

    failures = 0

    if int(meta['inputs']) != INPUT_COUNT:
        failures += 1
        print(f"FAIL: meta declares {meta['inputs']} inputs, expected {INPUT_COUNT}", file=sys.stderr)
    if len(raw_rows) != EXPECTED_ROWS:
        failures += 1
        print(f'FAIL: {len(raw_rows)} rows exported, expected {EXPECTED_ROWS}', file=sys.stderr)
    if len(z) != EXPECTED_WIRES:
        failures += 1
        print(f'FAIL: {len(z)} wires exported, expected {EXPECTED_WIRES}', file=sys.stderr)
    if failures:
        return 1

    rows = []
    for line in raw_rows:
        a, b, c = line.split(';')
        rows.append((parse_lf(a), parse_lf(b), parse_lf(c)))

    # 2. every row satisfied
    unsatisfied = []
    for index, (a, b, c) in enumerate(rows):
        if eval_lf(a, z) * eval_lf(b, z) % P != eval_lf(c, z):
            unsatisfied.append(index)
    if unsatisfied:
        failures += 1
        print(f'FAIL: {len(unsatisfied)} unsatisfied rows, first at {unsatisfied[:5]}', file=sys.stderr)
    else:
        print(f'matrices: all {len(rows)} rows satisfied by the exported witness')

    # 3. six-input binding
    declared = [int(v) for v in meta['input_values'].split(',')]
    if len(declared) != INPUT_COUNT:
        failures += 1
        print(f'FAIL: meta declares {len(declared)} input values', file=sys.stderr)
    elif z[:INPUT_COUNT] != declared:
        failures += 1
        print(f'FAIL: wires 0..{INPUT_COUNT - 1} are not the declared inputs', file=sys.stderr)
    else:
        print(f'matrices: the six external inputs are bound to wires 0..{INPUT_COUNT - 1}')

    # 4. mutation check on auxiliary wires.
    # Precompute, for every wire, the rows whose A, B or C form mentions it, so a
    # single-wire mutation only re-evaluates the affected rows.
    incidence = {}
    for index, (a, b, c) in enumerate(rows):
        for form in (a, b, c):
            for wire, _ in form[0]:
                incidence.setdefault(wire, set()).add(index)

    undetected = []
    for wire in range(INPUT_COUNT, len(z)):
        touched = incidence.get(wire)
        if not touched:
            undetected.append(wire)
            continue
        mutated = list(z)
        mutated[wire] = (mutated[wire] + 1) % P
        broken = False
        for index in touched:
            a, b, c = rows[index]
            if eval_lf(a, mutated) * eval_lf(b, mutated) % P != eval_lf(c, mutated):
                broken = True
                break
        if not broken:
            undetected.append(wire)
    if undetected:
        failures += 1
        print(f'FAIL: {len(undetected)} auxiliary wires are unconstrained, '
              f'first at {undetected[:5]}', file=sys.stderr)
    else:
        print(f'matrices: every one of the {len(z) - INPUT_COUNT} auxiliary wires '
              f'is constrained by at least one row')

    if failures:
        print(f'FAIL: {failures} matrix check(s) failed', file=sys.stderr)
        return 1
    print('matrices: all checks passed')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
