"""Exact binary-cylinder census for the two P1 scalar inverse feeders.

No sampling, floating point, machine-state classification, or external packages.
The symbolic cylinder tree and independent direct integer enumeration must agree.
"""
from fractions import Fraction


def root_children(side, cutoff):
    c, a, u, v = (12, 2, 3, 1) if side == 8 else (10, 1, 5, 2)
    if cutoff >= a - 1:
        t = a - 1
        yield (0, 0, t + 1,
               (side + t + 4 // (1 << t) - 1) // 2,
               8 + c // (1 << (t + 1)))
    for t in range(a, cutoff + 1):
        h = t - a + 1
        mod = 1 << h
        parity = 1 - (side + t) % 2
        residue = ((parity * (1 << (t - a)) - v)
                   * pow(u, -1, mod)) % mod
        numer = 16 * residue + side + t + (c * residue + 4) // (1 << t)
        assert (c * residue + 4) % (1 << t) == 0 and numer % 2 == 1
        yield residue, h, t + 1, (numer - 1) // 2, 8 * (1 << h) + u


def children(side, node, cutoff):
    q0, h, m, a, b = node
    assert b % 2 == 1
    for t in range(cutoff + 1):
        mod = 1 << (t + 1)
        parity = 1 - (side + m + t) % 2
        residue = ((parity * (1 << t) - a)
                   * pow(b, -1, mod)) % mod
        nq = q0 + (1 << h) * residue
        nh = h + t + 1
        numer = 16 * nq + side + m + t + (a + b * residue) // (1 << t)
        assert (a + b * residue) % (1 << t) == 0 and numer % 2 == 1
        yield nq, nh, m + t + 1, (numer - 1) // 2, 8 * (1 << nh) + b


def expected(side, cutoff, depth):
    assert side in (8, 9) and depth >= 1 and cutoff >= 2
    first = 2 - Fraction(1, 1 << (cutoff - 1 if side == 8 else cutoff))
    return first * (1 - Fraction(1, 1 << (cutoff + 1))) ** (depth - 1)


def check_cylinders(side, cutoff, max_depth):
    nodes = list(root_children(side, cutoff))
    for depth in range(1, max_depth + 1):
        actual = sum((Fraction(1, 1 << h) for _, h, _, _, _ in nodes),
                     Fraction(0))
        assert actual == expected(side, cutoff, depth)
        print("cylinder", side, cutoff, depth, len(nodes), actual)
        nodes = [child for node in nodes for child in children(side, node, cutoff)]


def check_direct(side, cutoff, max_depth, exponent):
    assert exponent >= max_depth * (cutoff + 1)
    c = 12 if side == 8 else 10
    totals = [0] * max_depth
    for q in range(1 << exponent):
        nodes = [(0, c * q + 4)]
        for depth in range(max_depth):
            next_nodes = []
            for m, z in nodes:
                for t in range(cutoff + 1):
                    if z % (1 << t):
                        continue
                    numerator = 16 * q + side + m + t + z // (1 << t)
                    if numerator % 2 == 1:
                        next_nodes.append((m + t + 1, numerator // 2))
            totals[depth] += len(next_nodes)
            nodes = next_nodes
    for depth, total in enumerate(totals, 1):
        actual = Fraction(total, 1 << exponent)
        assert actual == expected(side, cutoff, depth)
        print("direct", side, cutoff, depth, actual)


if __name__ == "__main__":
    for side in (8, 9):
        for cutoff in (2, 3, 4):
            check_cylinders(side, cutoff, 4)
        check_direct(side, 3, 3, 13)
