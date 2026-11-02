"""Uniform two-generation Sheep even-return inverse certificates.

Python 3.10+, standard library only. All periods checked by modular pow.
See README.md for the all-time mathematical soundness argument.
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class Node:
    shift: int
    offset: int
    divisor: int


ROOT = Node(0, 0, 1)
CASES = (
    (648, 53591297760, {ROOT: {(5, 2): Node(8, -1228, 2187)},
                         Node(8, -1228, 2187): {}}),
    (864, 14594696756640, {ROOT: {(3, 6): Node(10, -16576, 3483)},
                           Node(10, -16576, 3483): {}}),
    (1002, 89318829600, {ROOT: {(1, 1): Node(3, -2, 15),
                                (2, 2): Node(5, -68, 81)},
                            Node(3, -2, 15): {},
                            Node(5, -68, 81): {}}),
)


def high_h_cutoff(node, exponent, period):
    s, b, d = node.shift, node.offset, node.divisor
    for H in range(1, 20):
        m = d * 3**H
        if (pow(2, exponent + s, m) + b - d) % m:
            assert pow(2, period, m) == 1, (node, H, m)
            return H
    raise AssertionError(('no high-h cutoff', node))


def high_a_cutoff(D, C):
    for A in range(1, 80):
        q = D * (2 * A - 1) - 2 * C
        if 1 < q < 2**A and 2 * D < 2**A:
            return A
    raise AssertionError(('no high-a cutoff', D, C))


def exceptional_excluded(D, C, n):
    """Sufficient inequalities excluding all a>=1, stable for n'>=n."""
    c = 3 * D
    e = c.bit_length()
    assert (1 << (e - 1)) < c < (1 << e)
    assert n >= e + 2
    assert ((1 << e) - c) * (1 << (n - e)) > D * (n + 3) + abs(C)
    assert (1 << (n - e)) > 2 * D
    assert D * (n - e + 4) >= C


def verify_node(node, exponent, period):
    s, b, d = node.shift, node.offset, node.divisor
    assert d > 0 and d % 2 == 1 and s >= 0
    assert d == 1 or pow(2, period, d) == 1
    assert ((1 << (exponent+s)) + b) % d == 0
    assert (1 << (exponent+s)) + b > 10 * d
    H = high_h_cutoff(node, exponent, period)
    found = {}
    counts = []
    for h in range(H):
        D = d * 3**h
        C = (1 << h) * (b - d) + D
        A = high_a_cutoff(D, C)
        counts.append((h, A))
        exceptional_excluded(D, C, exponent+s+h)
        assert D == 1 or pow(2, period, D) == 1
        for a in range(1, A):
            den = D * ((1 << (a + 1)) + 1)
            B = 2*C - D*(2*a-1)
            assert pow(2, period, den) == 1, (node, h, a, den)
            valid_h = (pow(2, exponent+s, D) + b-d) % D == 0
            valid_a = (pow(2, exponent+s+h+1, 2*den) + B) % (2*den) == den
            if valid_h and valid_a:
                found[(h, a)] = Node(s+h+1+a, (1 << a)*B, den)
    return H, counts, found


def exact_even_parents(y):
    """Independent direct finite inverse cross-check at the base index."""
    parents = set()
    h = 0
    while (y-1) % (3**h) == 0:
        z = 1 + (1 << h) * ((y-1)//3**h)
        for a in range(1, z.bit_length()):
            den = (1 << (a+1)) + 1
            numerator = 2*z - 2*a + 1
            if numerator <= 0:
                break
            v, rem = divmod(numerator, den)
            if rem == 0 and v >= 5 and v % 2 == 1:
                parents.add((1 << a)*v)
            if 3*(1 << a)+a+3 == z:
                parents.add(3*(1 << a))
        h += 1
    return sorted(parents)


def main():
    for r, M, tree in CASES:
        print('Exponent family', r, '+', M, '* k')
        for node, expected in tree.items():
            H, cutoffs, found = verify_node(node, r, M)
            assert found == expected, (r, node, found, expected)
            value = ((1 << (r+node.shift)) + node.offset)//node.divisor
            actual = exact_even_parents(value)
            predicted = sorted(((1 << (r+child.shift)) + child.offset)//child.divisor
                               for child in expected.values())
            assert actual == predicted, (r, node, actual, predicted)
            print(' ', node, 'H=',H,'a cutoffs=',cutoffs,
                  'parent edges=',sorted(expected))
        assert set(tree) == {ROOT} | {child for child in tree[ROOT].values()}
        assert all(not edges for node,edges in tree.items() if node != ROOT)
        print('  PASS: all k >= 0; no even-return orbit 10 -> 2^j')


if __name__ == '__main__':
    main()
