"""Four source-meaningful exact finite predecessor cones for Sheep's E map.

This independently checks the universal modular certificates from uniform_138.py
and the literal E predecessor relation from exact_inverse.py.
The mathematical proof turning the modular checks into all-k statements is in
ROOT-FREE-CONES.md. Python calculations alone are not Lean kernel certificates.
"""
from math import gcd

import exact_inverse
import uniform_138 as cert


# For each source node, the dictionary enumerates ALL permitted predecessor
# parameter pairs (h, a) and their rational-exponential source nodes.
CONES = {
    138: {
        cert.ROOT: {(1, 1): cert.P1, (2, 2): cert.P2},
        cert.P1: {},
        cert.P2: {},
    },
    1218: {
        cert.ROOT: {(1, 1): cert.P1, (2, 2): cert.Node(5, -68, 81, 1, (11,), (16,))},
        cert.P1: {},
        cert.Node(5, -68, 81, 1, (11,), (16,)): {},
    },
    402: {
        cert.ROOT: {(1, 1): cert.Node(3, -2, 15, 2, (8, 10), (11, 15))},
        cert.Node(3, -2, 15, 2, (8, 10), (11, 15)):
            {(1, 4): cert.Node(9, -4688, 1485, 2, (16, 18), (25, 28))},
        cert.Node(9, -4688, 1485, 2, (16, 18), (25, 28)): {},
    },
    1738: {
        cert.Node(0, 0, 1, 2, (2, 5), (6, 7)):
            {(1, 1): cert.Node(3, -2, 15, 1, (8,), (11,))},
        cert.Node(3, -2, 15, 1, (8,), (11,)):
            {(0, 2): cert.Node(6, -196, 135, 3, (12, 14, 16), (18, 21, 24))},
        cert.Node(6, -196, 135, 3, (12, 14, 16), (18, 21, 24)): {},
    },
}


def node_value(r, node, k):
    numerator = (1 << (r + 4860 * k + node.s)) + node.b
    quotient, remainder = divmod(numerator, node.d)
    assert remainder == 0
    return quotient


def check_class(r, nodes):
    cert.R = r
    cert.M = 4860
    checks = 0
    period_representatives = 0
    assert all(child in nodes for edges in nodes.values() for child in edges.values())
    for node, children in nodes.items():
        expected = {p: (n.s, n.b, n.d) for p, n in children.items()}
        cert.verify_node(node, expected)
        for h, bound in enumerate(node.limits):
            for a in range(1, bound):
                _, _, period = cert.eligible_k(node, h, a)
                checks += 1
                period_representatives += period
        for h, a in children:
            good, derived, period = cert.eligible_k(node, h, a)
            assert derived == expected[(h, a)]
            assert good == list(range(period)), (r, node, h, a, good, period)
            assert period == 1, (r, node, h, a, period)
        # Exact, checked order of 2 proves this is a complete k-period
        # for the rational-node integrality predicate.
        p = cert.cycle_modulus(node.d)
        for k in range(p):
            assert (pow(2, r + 4860 * k + node.s, node.d) + node.b) % node.d == 0
        assert node_value(r, node, 0) > 10
        # Finite independent regression only; the all-k theorem follows
        # from the period and high-a/exceptional bounds in verify_node.
        for k in (0, 1):
            target = node_value(r, node, k)
            actual = set(exact_inverse.even_parents(target))
            want = {node_value(r, child, k) for child in children.values()}
            assert actual == want, (r, node, k, actual, want)
            for parent in want:
                assert exact_inverse.even_next(parent) == target
    root = next(iter(nodes))
    assert node_value(r, root, 0) == (1 << r)
    assert all(node_value(r, node, 0) != 10 for node in nodes)
    print(
        f"PASS r={r}: {len(nodes)}-state rooted inverse cone; "
        f"{checks} finite (h,a) families screened; "
        f"{period_representatives} complete k-period representatives checked"
    )


if __name__ == "__main__":
    for r, graph in CONES.items():
        check_class(r, graph)
