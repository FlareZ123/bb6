"""Exact certificate for two additional seventh-stratum inverse-tree families.

This file certifies:
  * 26 h=1,a=3 classes with a seven-node finite inverse tree;
  * 22 h=3,a=6 classes with a three-node finite inverse tree.

Together with inverse_tree_44_classes_certificate.py, this gives 92
progression classes in the combined presentation (the h=7,a=4 nine classes
lift to 27 classes modulo T2).

Only Python's standard library is used. Lean source formalization is pending.
"""
from collections import deque
from fractions import Fraction
from math import gcd, lcm

J = 1458
T1_EXPECTED = 80_313_433_200
T3_EXPECTED = 150_151_201_200
T_PRIOR_EXPECTED = 1_178_100

PRIOR_E = (
    *((r, 4860) for r in (138, 402, 1218, 1738)),
    (118, 14580), (246, 24300), (558, 8100), (846, 8100),
    (702, 11340), (194, 24300), (5054, 24300), (366, 8100),
    (1986, 8100), (374, 8100), (1994, 8100), (482, 43740),
    (9230, 43740), (495, 43740), (9243, 43740), (819, 14580),
    (3735, 14580), (188, 55080), (190, 306180), (220, 55080),
    (262, 53460), (442, 1837080), (624, 29160), (648, 122472),
)

R1 = (
    50, 58, 170, 178, 230, 238, 350, 430, 490, 598, 610, 710, 770,
    778, 790, 850, 890, 898, 958, 1030, 1070, 1078, 1130, 1138, 1210, 1250,
)
R3 = (
    40, 124, 152, 236, 292, 320, 376, 404, 544, 572, 628,
    656, 740, 796, 824, 880, 992, 1048, 1076, 1132, 1160, 1244,
)

# Earlier two-node families, used for disjointness and the combined density.
R2 = (28, 64, 136, 244, 280, 352, 388, 568, 604,
      676, 784, 892, 928, 1000, 1036, 1108, 1252)
R4 = (8, 188, 368, 428, 548, 608, 968, 1088, 1148)
T2 = 31_426_995_600
T4 = 10_475_665_200
T3_PRIOR = 1_178_100

ROOT_GENERIC_A = (2, 5, 7, 9, 11, 13, 15, 16)
ROOT_SPECIAL_S = (3, 5, 7, 9, 10, 12, 14, 16)

FAMILIES = {
    "h1a3": {
        "t0": 50, "residues": R1, "T": T1_EXPECTED,
        "nodes": 7, "edges": 6, "tree_lcm": T1_EXPECTED,
    },
    "h3a6": {
        "t0": 40, "residues": R3, "T": T3_EXPECTED,
        "nodes": 3, "edges": 2, "tree_lcm": 30_030_240_240,
    },
}


def factor(n: int) -> dict[int, int]:
    assert n >= 1
    out: dict[int, int] = {}
    d = 2
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            out[d] = e
        d = 3 if d == 2 else d + 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def merge_factors(*items: dict[int, int]) -> dict[int, int]:
    out: dict[int, int] = {}
    for item in items:
        for p, e in item.items():
            if e:
                out[p] = out.get(p, 0) + e
    return out


def phi_factorization(n_factors: dict[int, int]) -> dict[int, int]:
    out: dict[int, int] = {}
    for p, e in n_factors.items():
        if e > 1:
            out[p] = out.get(p, 0) + e - 1
        for q, f in factor(p - 1).items():
            out[q] = out.get(q, 0) + f
    return out


def value_from_factors(factors: dict[int, int]) -> int:
    value = 1
    for p, e in factors.items():
        value *= p**e
    return value


def order_two(modulus: int, modulus_factors: dict[int, int]) -> int:
    phi_factors = phi_factorization(modulus_factors)
    order = value_from_factors(phi_factors)
    for p in phi_factors:
        while order % p == 0 and pow(2, order // p, modulus) == 1:
            order //= p
    assert pow(2, order, modulus) == 1
    return order


def valuation3(n: int) -> int:
    assert n != 0
    n = abs(n)
    e = 0
    while n % 3 == 0:
        n //= 3
        e += 1
    return e


def generic_cutoff(C: int, B: int, h: int) -> tuple[int, int, int]:
    D = C * 3**h

    def K(a: int) -> int:
        return 2 ** (h + 1) * (C - B) + D * (2 * a - 3)

    A = 1
    while not (K(A) > 1 and K(A) < 2**A and 2 * D <= 2**A):
        A += 1
    assert K(A) % 2 == 1
    return A, K(A), D


def special_cutoff(C: int, B: int, h: int) -> tuple[int, int, int]:
    D = C * 3**h

    def L(a: int) -> int:
        return D * (a + 2) + 2**h * (C - B)

    A = 1
    while not (L(A) > 1 and L(A) < 2**A and D <= 2**A):
        A += 1
    return A, L(A), D


def build_tree(t0: int):
    root = {"id": 0, "s": 0, "B": 0, "C": 1, "fC": {}, "depth": 0}
    nodes = [root]
    by_key = {(0, 0, 1): 0}
    queue = deque([0])
    edges = []
    row_periods = []
    row_moduli = []
    valuation_periods = []
    generic_cutoffs = []
    special_cutoffs = []

    while queue:
        node_id = queue.popleft()
        node = nodes[node_id]
        s, B, C = node["s"], node["B"], node["C"]
        j0 = J * t0
        numerator = 2**(j0 + s) + B
        assert numerator % C == 0
        y = numerator // C
        assert y > 10 and y % 2 == 0
        r = valuation3(y - 1)
        node["r"] = r

        k = r + valuation3(C) + 1
        phi3 = 2 * 3 ** (k - 1)
        p3 = phi3 // gcd(phi3, J)
        assert pow(2, J * p3, 3**k) == 1
        valuation_periods.append((node_id, k, p3))

        outgoing = []
        for h in range(r + 1):
            D = C * 3**h
            A, K_A, _ = generic_cutoff(C, B, h)
            generic_cutoffs.append((node_id, h, A, K_A, D))

            for a in range(1, A):
                M = 2 ** (a + 1) + 1
                modulus = D * M
                n_factors = merge_factors(
                    node["fC"],
                    ({3: h} if h else {}),
                    factor(M),
                )
                assert value_from_factors(n_factors) == modulus
                order = order_two(modulus, n_factors)
                period = order // gcd(order, J)
                assert pow(2, J * period, modulus) == 1
                row_periods.append(period)
                row_moduli.append(modulus)

                K = 2 ** (h + 1) * (C - B) + D * (2 * a - 3)
                diff = 2 ** (j0 + s + h + 1) - K
                if diff % modulus == 0:
                    v = diff // modulus
                    assert v >= 5 and v % 2 == 1
                    s2 = s + a + h + 1
                    B2 = 2**a * (
                        2 ** (h + 1) * (B - C)
                        + C * 3**h * (3 - 2 * a)
                    )
                    C2 = modulus
                    key = (s2, B2, C2)
                    child_id = by_key.get(key)
                    if child_id is None:
                        child_id = len(nodes)
                        by_key[key] = child_id
                        nodes.append({
                            "id": child_id, "s": s2, "B": B2, "C": C2,
                            "fC": n_factors, "depth": node["depth"] + 1,
                        })
                        queue.append(child_id)
                    outgoing.append((h, a, child_id))
                    edges.append((node_id, child_id, h, a))

            S, L_S, _ = special_cutoff(C, B, h)
            special_cutoffs.append((node_id, h, S, L_S, D))
            lhs = 2 ** (j0 + s + h)
            for a in range(1, S):
                L = D * (a + 2) + 2**h * (C - B)
                assert 3 * D * 2**a + L < lhs

        node["outgoing"] = outgoing

    T_tree = lcm(*row_periods, *(p for _, _, p in valuation_periods))
    T_prior = lcm(*(p // gcd(p, J) for _, p in PRIOR_E))
    T = lcm(T_tree, T_prior)

    return {
        "nodes": nodes, "edges": edges, "row_periods": row_periods,
        "row_moduli": row_moduli, "valuation_periods": valuation_periods,
        "generic_cutoffs": generic_cutoffs, "special_cutoffs": special_cutoffs,
        "T_tree": T_tree, "T_prior": T_prior, "T": T,
    }


def node_r_at_t(t: int, node: dict) -> int:
    C, B, s = node["C"], node["B"], node["s"]
    c3 = valuation3(C)
    for r in range(20):
        modulus = 3 ** (c3 + r + 1)
        if (pow(2, J * t + s, modulus) + B - C) % modulus != 0:
            return r
    raise AssertionError("valuation search bound exceeded")


def verify_tree_at_t(t: int, tree: dict) -> None:
    nodes, edges = tree["nodes"], tree["edges"]
    expected = {
        node["id"]: {(h, a) for src, dst, h, a in edges if src == node["id"]}
        for node in nodes
    }
    for node in nodes:
        C, B, s = node["C"], node["B"], node["s"]
        assert (pow(2, J * t + s, C) + B) % C == 0
        assert node_r_at_t(t, node) == node["r"]
        hits = set()
        for h in range(node["r"] + 1):
            A = next(A for nid, hh, A, _, _ in tree["generic_cutoffs"]
                     if nid == node["id"] and hh == h)
            D = C * 3**h
            for a in range(1, A):
                N = D * (2 ** (a + 1) + 1)
                K = 2 ** (h + 1) * (C - B) + D * (2 * a - 3)
                if pow(2, J * t + s + h + 1, N) == K % N:
                    hits.add((h, a))
        assert hits == expected[node["id"]]


def certify() -> None:
    T_prior = lcm(*(p // gcd(p, J) for _, p in PRIOR_E))
    assert T_prior == T_PRIOR_EXPECTED

    all_families = {}
    for name, spec in FAMILIES.items():
        tree = build_tree(spec["t0"])
        assert len(tree["nodes"]) == spec["nodes"]
        assert len(tree["edges"]) == spec["edges"]
        assert tree["T_tree"] == spec["tree_lcm"]
        assert tree["T"] == spec["T"]
        assert tree["T"] % 1260 == 0

        # The common period freezes every row and every valuation.
        assert all(pow(2, J * tree["T"], N) == 1 for N in tree["row_moduli"])
        for _, k, _ in tree["valuation_periods"]:
            assert pow(2, J * tree["T"], 3**k) == 1

        # Verify the complete graph at every base residue.
        for t in spec["residues"]:
            verify_tree_at_t(t, tree)
            assert all((J * t - base) % period != 0 for base, period in PRIOR_E)

        all_families[name] = tree

    h1 = all_families["h1a3"]
    h3 = all_families["h3a6"]
    assert len(R1) == 26 and len(R3) == 22
    assert len(h1["row_periods"]) == 163
    assert len(set(h1["row_moduli"])) == 160
    assert len(set(3**k for _, k, _ in h1["valuation_periods"])) == 4
    assert len(h3["row_periods"]) == 107
    assert len(set(h3["row_moduli"])) == 105
    assert len(set(3**k for _, k, _ in h3["valuation_periods"])) == 3

    # The four first-parent sectors are disjoint modulo 1260.
    bases = (*R1, *R3, *R2, *R4)
    residues_mod_1260 = [t % 1260 for t in bases]
    assert len(residues_mod_1260) == len(set(residues_mod_1260))
    assert len(bases) == 74

    # Every progression family is disjoint from all old E-cones.
    for name, spec in FAMILIES.items():
        T = spec["T"]
        for _, period in PRIOR_E:
            assert T % (period // gcd(period, J)) == 0

    density = (
        Fraction(26, J * T1_EXPECTED)
        + Fraction(22, J * T3_EXPECTED)
        + Fraction(17, J * T2)
        + Fraction(9, J * T4)
    )
    assert density == Fraction(14533, 11329133357341800)

    print("PASS: h1a3: 26 residues, 7-node/6-edge tree, T=80,313,433,200")
    print("PASS: h3a6: 22 residues, 3-node/2-edge tree, T=150,151,201,200")
    print("PASS: h7a2/h7a4: 17 + 9 base residues, two-node trees (see 44-class checker)")
    print("PASS: all base residue graphs exactly match their finite inverse trees")
    print("PASS: all modular and 3-adic periods freeze; prior 28 E-cones are disjoint")
    print("PASS: all 74 base residues are pairwise distinct modulo 1260")
    print(f"PASS: combined density = {density} = {float(density):.12g}")


if __name__ == "__main__":
    certify()
