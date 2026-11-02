"""Exact-arithmetic audit of the shared P1 affine scanner's closed certificates.

The verification below is computational evidence. The mathematical power-band
lemma is independently Lean-verified in PowerCertificate.lean. None of the
unverified inverse cones is promoted to a formal theorem by this script.
"""
from collections import Counter
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'agent4-p1-cone2398'))
from uniform_scan import Aff, all_positive_g_ancestors, check_residue


def power_leaves(r):
    stack = [(Aff(131072, 131056 - 2 * r), Aff(0, 3))]
    powers = []
    while stack:
        b, d = stack.pop()
        for k, u in all_positive_g_ancestors(b, d):
            x, y = k * 2 - 4, u + 4
            if y.residue(2) == 0:
                powers.append(x + 12)
            elif y.residue(2) == 1 and x.residue(4) == 0:
                stack.append((x, y))
    return powers


def main():
    total = Counter()
    extrema = {'min_a': None, 'max_a': None, 'min_c': None, 'max_c': None}
    examples = {}
    all_powers = []
    for sector, start in ((2, 34), (14, 30)):
        closed = 0
        count = 0
        for r in range(start, 65536, 16):
            is_closed, status, _, leaves = check_residue(r)
            if not is_closed:
                continue
            closed += 1
            powers = power_leaves(r)
            assert len(powers) == leaves['power'] == leaves['mod4'], r
            count += len(powers)
            for expr in powers:
                a, c = expr.a, expr.c
                assert 65832 <= a <= 130896, (r, expr)
                assert 8 <= c <= 130290, (r, expr)
                for field, value, is_min in (
                    ('min_a', a, True), ('max_a', a, False),
                    ('min_c', c, True), ('max_c', c, False),
                ):
                    prev = extrema[field]
                    if prev is None or ((value < prev) if is_min else (value > prev)):
                        extrema[field] = value
                        examples[field] = r
                all_powers.append((a, c))
        total[(sector, 'closed')] = closed
        total[(sector, 'power')] = count
    assert total[(2, 'closed')] == 2845
    assert total[(14, 'closed')] == 2419
    assert total[(2, 'power')] == 39735
    assert total[(14, 'power')] == 36429
    assert extrema == dict(min_a=65832, max_a=130896, min_c=8, max_c=130290)
    assert len(set(all_powers)) == len(all_powers)
    print('closed counts:', dict(total))
    print('power leaf coefficient extrema:', extrema)
    print('example critical residues attaining extrema:', examples)
    print('all 76164 candidate leaves lie in the Lean-proved universal rectangle')


if __name__ == '__main__':
    main()
