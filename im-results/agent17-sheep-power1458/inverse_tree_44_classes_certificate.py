"""Exact certificate for 44 seventh-stratum blank-root exclusion classes.

For j=1458*t, two different two-node inverse trees are certified:
  * h=7,a=2 source type, period T2=31426995600, 17 residues;
  * h=7,a=4 source type, period T4=10475665200, 9 residues.
Since T2=3*T4, the union is 44 distinct t-residues modulo T2.

Only Python's standard library is used.  Exact source-level Lean proof and
axiom audit remain pending.
"""
from math import gcd, lcm

J = 1458
T4 = 10_475_665_200
T2 = 31_426_995_600
T_PRIOR = 1_178_100
T_COMMON = T2

PRIOR_E = (
    *((r, 4860) for r in (138, 402, 1218, 1738)),
    (118, 14580), (246, 24300), (558, 8100), (846, 8100),
    (702, 11340), (194, 24300), (5054, 24300), (366, 8100),
    (1986, 8100), (374, 8100), (1994, 8100), (482, 43740),
    (9230, 43740), (495, 43740), (9243, 43740), (819, 14580),
    (3735, 14580), (188, 55080), (190, 306180), (220, 55080),
    (262, 53460), (442, 1837080), (624, 29160), (648, 122472),
)

ROOT_GENERIC_A = (2, 5, 7, 9, 11, 13, 15, 16)
ROOT_SPECIAL_S = (3, 5, 7, 9, 10, 12, 14, 16)

R2 = (28, 64, 136, 244, 280, 352, 388, 568, 604,
      676, 784, 892, 928, 1000, 1036, 1108, 1252)
R4 = (8, 188, 368, 428, 548, 608, 968, 1088, 1148)

TYPES = {
    "h7a2": {
        "h": 7, "a": 2, "s": 10, "B": -9772, "C": 19683,
        "generic_A": 20, "special_S": 19,
        "tree_period": 6_285_399_120, "period": T2,
    },
    "h7a4": {
        "h": 7, "a": 4, "s": 12, "B": -179056, "C": 72171,
        "generic_A": 22, "special_S": 21,
        "tree_period": 2_095_133_040, "period": T4,
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
    for p in factor(order):
        assert pow(2, order // p, modulus) != 1
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


def exact_type_period(kind: str) -> tuple[int, int, list[int], list[int]]:
    """Return tree LCM, row count, row moduli, valuation moduli."""
    typ = TYPES[kind]
    periods = []
    moduli = []

    # Root node Y0=2^(1458*t): 70 possible low-a rows.
    for h, A in enumerate(ROOT_GENERIC_A):
        for a in range(1, A):
            M = 2 ** (a + 1) + 1
            N = 3**h * M
            nf = merge_factors(({3: h} if h else {}), factor(M))
            order = order_two(N, nf)
            p = order // gcd(order, J)
            assert pow(2, J * p, N) == 1
            periods.append(p)
            moduli.append(N)

    # The one intermediate affine node: h=0 only.
    C = typ["C"]
    A = typ["generic_A"]
    cf = factor(C)
    for a in range(1, A):
        M = 2 ** (a + 1) + 1
        N = C * M
        nf = merge_factors(cf, factor(M))
        order = order_two(N, nf)
        p = order // gcd(order, J)
        assert pow(2, J * p, N) == 1
        periods.append(p)
        moduli.append(N)

    # Freeze root r=7 (mod 3^8) and the intermediate node r=0.
    valuation_moduli = [3**8, 3 ** (valuation3(C) + 1)]
    for m in valuation_moduli:
        phi3 = 2 * (m // 3)
        p = phi3 // gcd(phi3, J)
        assert pow(2, J * p, m) == 1
        periods.append(p)

    return lcm(*periods), len(moduli), moduli, valuation_moduli


def root_parent_hits(t: int) -> list[tuple[int, int]]:
    hits = []
    j = J * t
    for h, A in enumerate(ROOT_GENERIC_A):
        D = 3**h
        for a in range(1, A):
            M = 2 ** (a + 1) + 1
            N = D * M
            K = 2 ** (h + 1) + D * (2 * a - 3)
            if pow(2, j + h + 1, N) == K % N:
                hits.append((h, a))
    return hits


def node_has_parent(t: int, typ: dict) -> bool:
    C, B, s, A = typ["C"], typ["B"], typ["s"], typ["generic_A"]
    j = J * t
    for a in range(1, A):
        N = C * (2 ** (a + 1) + 1)
        K = 2 * (C - B) + C * (2 * a - 3)
        if pow(2, j + s + 1, N) == K % N:
            return True
    return False


def node_has_r_zero(t: int, typ: dict) -> bool:
    C, B, s = typ["C"], typ["B"], typ["s"]
    c3 = valuation3(C)
    modulus = 3 ** (c3 + 1)
    return (pow(2, J * t + s, modulus) + B - C) % modulus != 0


def verify_cutoffs() -> None:
    for h, A in enumerate(ROOT_GENERIC_A):
        A0, K0, D = generic_cutoff(1, 0, h)
        assert A0 == A and 1 < K0 < 2**A and 2 * D <= 2**A
    for h, S in enumerate(ROOT_SPECIAL_S):
        S0, L0, D = special_cutoff(1, 0, h)
        assert S0 == S and 1 < L0 < 2**S and D <= 2**S
        for a in range(1, S):
            rhs = 3 * D * 2**a + D * (a + 2) + 2**h
            assert rhs < 2 ** (J + h)

    for typ in TYPES.values():
        A, K0, D = generic_cutoff(typ["C"], typ["B"], 0)
        assert A == typ["generic_A"]
        assert 1 < K0 < 2**A and 2 * D <= 2**A
        S, L0, D = special_cutoff(typ["C"], typ["B"], 0)
        assert S == typ["special_S"]
        assert 1 < L0 < 2**S and D <= 2**S
        lhs = 2 ** (J * (28 if typ["h"] == 7 and typ["a"] == 2 else 8) + typ["s"])
        for a in range(1, S):
            rhs = 3 * D * 2**a + D * (a + 2) + (typ["C"] - typ["B"])
            assert rhs < lhs


def certify() -> None:
    assert len(PRIOR_E) == 28
    Ttree2, rows2, mods2, vals2 = exact_type_period("h7a2")
    Ttree4, rows4, mods4, vals4 = exact_type_period("h7a4")
    Tprior = lcm(*(p // gcd(p, J) for _, p in PRIOR_E))
    T2 = lcm(Ttree2, Tprior)
    T4 = lcm(Ttree4, Tprior)

    assert Tprior == T_PRIOR
    assert Ttree2 == TYPES["h7a2"]["tree_period"]
    assert Ttree4 == TYPES["h7a4"]["tree_period"]
    assert T2 == TYPES["h7a2"]["period"] == T2_EXPECTED
    assert T4 == TYPES["h7a4"]["period"] == T4_EXPECTED
    assert T2 == 3 * T4 == T_COMMON
    assert factor(T2) == {
        2: 4, 3: 5, 5: 2, 7: 1, 11: 1, 13: 1, 17: 1, 19: 1,
    }

    # The 44 residue classes modulo T2.
    residues4 = tuple(r + q * T4 for r in R4 for q in range(3))
    residues = tuple(sorted((*R2, *residues4)))
    assert len(R2) == 17 and len(R4) == 9
    assert len(residues) == 44 and len(set(residues)) == 44
    assert all(0 <= r < T2 for r in residues)
    assert T2 % 1260 == 0

    # Every class has exactly one authentic generic first parent, and its
    # intermediate affine node has r=0 and no generic predecessor.
    for t in residues:
        hits = root_parent_hits(t)
        if t in R2:
            kind = "h7a2"
            assert hits == [(7, 2)]
        else:
            kind = "h7a4"
            assert hits == [(7, 4)]
        typ = TYPES[kind]
        assert node_has_r_zero(t, typ)
        assert not node_has_parent(t, typ)

    # The common period freezes every one of the 110 modular tests.
    all_moduli = (*mods2, *mods4)
    valuation_moduli = (*vals2, *vals4)
    assert len(mods2) == 89 and len(mods4) == 91
    assert len(all_moduli) == 180 and len(set(all_moduli)) == 110
    assert len(set(valuation_moduli)) == 3
    assert all(pow(2, J * T2, N) == 1 for N in all_moduli)
    assert all(pow(2, J * T2, M) == 1 for M in valuation_moduli)

    # Every base class is disjoint from the 28 prior E progressions, and T2
    # preserves this disjointness for all subsequent t in the same class.
    for t in residues:
        for base, period in PRIOR_E:
            assert (J * t - base) % period != 0
    for _, period in PRIOR_E:
        assert T2 % (period // gcd(period, J)) == 0

    verify_cutoffs()

    # Check the unique first-parent cofactors at the smallest bases.
    n2 = 2 ** (J * min(R2) + 8) - 2443
    n4 = 2 ** (J * min(R4) + 8) - 11191
    assert n2 % 19683 == 0 and n4 % 72171 == 0
    v2, v4 = n2 // 19683, n4 // 72171
    assert v2 >= 5 and v2 % 2 == 1
    assert v4 >= 5 and v4 % 2 == 1

    exponent_period = J * T2
    assert exponent_period == 45_820_559_584_800
    assert exponent_period % 44 == 0
    density_denominator = exponent_period // 44
    assert density_denominator == 1_041_376_354_200

    print(f"PASS: T2={T2:,}, T4={T4:,}, T2=3*T4")
    print(f"PASS: 17 h7a2 classes + 27 lifted h7a4 classes = {len(residues)}")
    print(f"PASS: {len(mods2) + len(mods4)} period rows across {len(set(all_moduli))} distinct moduli")
    print("PASS: all 44 classes have exactly one genuine first parent")
    print("PASS: all 44 intermediate nodes have v3(Y-1)=0 and no generic parent")
    print("PASS: all 110 distinct moduli and all three valuation moduli divide T2")
    print("PASS: exceptional parents excluded by the 9 generic/special cutoff pairs")
    print("PASS: all 44 classes disjoint from the 28 prior E-cone progressions")
    print(f"PASS: density among exponent indices = 1/{density_denominator:,}")
    print("Candidate theorem: every listed residue r modulo T2 is blank-root unreachable.")


T2_EXPECTED = 31_426_995_600
T4_EXPECTED = 10_475_665_200

if __name__ == "__main__":
    certify()
