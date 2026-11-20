"""Exact two-node inverse-tree certificate for the t == 8 (mod T) class.

For j=1458*t, this certifies the complete original-source inverse graph for
t=8 and computes a common period T=10475665200 that preserves every
3-adic valuation and every finite generic-parent congruence.  The 28 older
E-cone progressions are explicitly excluded.

Only Python's standard library is used.  Lean source formalization remains
a separate pending obligation.
"""
from collections import deque
from math import gcd, lcm

J = 1458
T_EXPECTED = 10_475_665_200
T_TREE_EXPECTED = 2_095_133_040
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
    order = value_from_factors(phi_factorization(modulus_factors))
    for p in phi_factorization(modulus_factors):
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
    # K(a+1)=K(a)+2D, so these bounds persist for all a>=A.
    return A, K(A), D


def special_cutoff(C: int, B: int, h: int) -> tuple[int, int, int]:
    D = C * 3**h

    def L(a: int) -> int:
        return D * (a + 2) + 2**h * (C - B)

    A = 1
    while not (L(A) > 1 and L(A) < 2**A and D <= 2**A):
        A += 1
    # L(a+1)=L(a)+D, so these bounds persist for all a>=A.
    return A, L(A), D


def build_tree():
    t0 = 8
    j0 = J * t0
    root = {
        "id": 0, "s": 0, "B": 0, "C": 1,
        "fC": {}, "depth": 0,
    }
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
        numerator = 2 ** (j0 + s) + B
        assert numerator % C == 0
        y = numerator // C
        assert y > 10 and y % 2 == 0
        r = valuation3(y - 1)
        node["r"] = r

        # Freeze v_3(Y(t)-1) modulo 3^(r+v_3(C)+1).
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

            # For every a>=A, K(a) is odd and 1<K(a)<2^a.
            # Agent40's no_power_signed_small_odd excludes these rows.
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
                assert K % 2 == 1
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
                    child_key = (s2, B2, C2)
                    child_id = by_key.get(child_key)
                    if child_id is None:
                        child_id = len(nodes)
                        by_key[child_key] = child_id
                        nodes.append({
                            "id": child_id, "s": s2, "B": B2, "C": C2,
                            "fC": n_factors, "depth": node["depth"] + 1,
                        })
                        queue.append(child_id)

                    child_num = 2 ** (j0 + s2) + B2
                    assert child_num % C2 == 0
                    assert child_num // C2 == 2**a * v
                    outgoing.append((h, a, child_id))
                    edges.append((node_id, child_id, h, a, v))

            # Exceptional source x=3*2^a:
            # 2^(j+s+h)=3D*2^a+L(a), L(a)=D(a+2)+2^h(C-B).
            S, L_S, _ = special_cutoff(C, B, h)
            special_cutoffs.append((node_id, h, S, L_S, D))
            lhs_at_t8 = 2 ** (j0 + s + h)
            for a in range(1, S):
                L = D * (a + 2) + 2**h * (C - B)
                rhs = 3 * D * 2**a + L
                assert rhs < lhs_at_t8

            # For a>=S, 1<L(a)<2^a and D<=2^a. If a<=j+s+h,
            # the equation forces 2^a|L(a), impossible. If a is larger,
            # the right side exceeds the left side.

        node["outgoing"] = outgoing

    return (nodes, edges, row_periods, row_moduli, valuation_periods,
            generic_cutoffs, special_cutoffs)


def certify() -> None:
    (nodes, edges, row_periods, row_moduli, valuation_periods,
     generic_cutoffs, special_cutoffs) = build_tree()

    T_tree = lcm(*row_periods, *(p for _, _, p in valuation_periods))
    T_prior = lcm(*(p // gcd(p, J) for _, p in PRIOR_E))
    T = lcm(T_tree, T_prior)

    assert T_tree == T_TREE_EXPECTED
    assert T_prior == T_PRIOR_EXPECTED
    assert T == T_EXPECTED
    assert factor(T) == {
        2: 4, 3: 4, 5: 2, 7: 1, 11: 1, 13: 1, 17: 1, 19: 1,
    }
    assert len(nodes) == 2 and len(edges) == 1
    assert nodes[0]["outgoing"] == [(7, 4, 1)]
    assert nodes[1]["outgoing"] == []
    assert nodes[0]["r"] == 7 and nodes[1]["r"] == 0
    assert len(row_periods) == 91
    assert len(valuation_periods) == 2
    assert len(generic_cutoffs) == 9
    assert len(special_cutoffs) == 9
    assert all(v >= 5 and v % 2 == 1 for *_, v in edges)

    # The common t-period freezes all 91 generic congruences.
    assert all(pow(2, J * T, modulus) == 1 for modulus in row_moduli)
    for _, k, _ in valuation_periods:
        assert pow(2, J * T, 3**k) == 1

    # The new class is disjoint from all 28 earlier E-cone progressions.
    assert len(PRIOR_E) == 28
    for base, period in PRIOR_E:
        assert (J * 8 - base) % period != 0
        assert T % (period // gcd(period, J)) == 0

    # The unique edge has the exact affine child displayed in the note.
    assert (nodes[1]["s"], nodes[1]["B"], nodes[1]["C"]) == (
        12, -179056, 72171
    )
    assert nodes[1]["r"] == 0

    print(f"PASS: T={T:,} = {factor(T)}")
    print(f"PASS: t=8 has exactly one generic parent (h=7,a=4)")
    print("PASS: terminal affine node (s=12,B=-179056,C=72171) has no parents")
    print(f"PASS: {len(row_periods)} exact modular periods; all divide T")
    print(f"PASS: {len(valuation_periods)} 3-adic valuation periods; all divide T")
    print("PASS: 9 generic and 9 exceptional cutoffs; no special parent")
    print("PASS: all 28 prior E-cone progressions are disjoint")
    print("Candidate theorem: for every k>=0, 2^(1458*(8+T*k)) is not EvenReach from 10.")


if __name__ == "__main__":
    certify()
