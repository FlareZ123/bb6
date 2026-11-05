#!/usr/bin/env python3
"""Exact modular certificate for seven additional Sheep first-even inverse cones.

Python 3.10+ standard library. Every periodic congruence is checked over a
provably complete period. The all-a and all-j arguments are in README.md.
No finite forward-orbit cutoff or floating-point approximation is used.
"""
from itertools import combinations
from fractions import Fraction
from math import gcd, lcm

# Each entry: (base exponent, period, (s,b,d) nodes, (from,h,a,to) edges).
# A node denotes the exact integer y(j)=(2**(j+s)+b)//d.
# Case data are new; verifier logic is adapted (credited) from Agent 16's
# five-cone arithmetic verifier. Nodes use (2^(j+s)+b)/d.
CASES = (
    (188, 55080,
     ((0, 0, 1), (5, -104, 51), (7, -518, 255)),
     ((0, 1, 3, 1), (1, 0, 1, 2))),
    (190, 306180,
     ((0, 0, 1), (3, -2, 15), (6, -196, 135), (9, -3188, 1215)),
     ((0, 1, 1, 1), (1, 0, 2, 2), (2, 0, 2, 3))),
    (220, 55080,
     ((0, 0, 1), (5, -104, 51), (7, -518, 255), (10, -7204, 2295)),
     ((0, 1, 3, 1), (1, 0, 1, 2), (2, 0, 2, 3))),
    (262, 53460,
     ((0, 0, 1), (3, -2, 15), (6, -196, 135), (11, -21392, 4455)),
     ((0, 1, 1, 1), (1, 0, 2, 2), (2, 0, 4, 3))),
    (442, 1837080,
     ((0, 0, 1), (3, -2, 15), (6, -196, 135)),
     ((0, 1, 1, 1), (1, 0, 2, 2))),
    (624, 29160,
     ((0, 0, 1), (5, -68, 81), (8, -706, 1215)),
     ((0, 2, 2, 1), (1, 1, 1, 2))),
    (648, 122472,
     ((0, 0, 1), (8, -1228, 2187)),
     ((0, 5, 2, 1),)),
)
PRIOR_E = tuple((r, 4860) for r in (138, 402, 1218, 1738)) + (
    (118, 14580), (246, 24300), (558, 8100), (846, 8100),
    (702, 11340),
)
# Literal five-inverse-step certificates for the ordinary Sheep F map.
# Each valuation sequence is a genuine path, from 2^j backward 5 steps.
F_PATHS = {
    188: (0, 3, 1, 0, 0),
    190: (0, 1, 2, 2, 0),
    220: (0, 3, 1, 2, 0),
    262: (0, 1, 2, 4, 0),
    442: (0, 1, 2, 0, 0),
    624: (0, 0, 2, 0, 1),
    648: (0, 0, 0, 0, 0),
}


def order_two(modulus: int) -> int:
    """Return the exact order of 2 modulo a positive odd modulus."""
    assert modulus >= 1 and modulus % 2 == 1
    if modulus == 1:
        return 1
    x = 2 % modulus
    order = 1
    while x != 1:
        x = (x * 2) % modulus
        order += 1
    return order


def v3(value: int) -> int:
    assert value > 0
    n = 0
    while value % 3 == 0:
        n += 1
        value //= 3
    return n


def section_next(t: int) -> int:
    a = (t & -t).bit_length() - 1
    u = t >> a
    assert t >= 5 and u >= 3
    return t + a + (3 if u == 3 else (u - 1) // 2)


def first_even(t: int) -> int:
    assert t >= 6 and t % 2 == 0
    z = section_next(t)
    w = z - 1
    h = (w & -w).bit_length() - 1
    return 1 + pow(3, h) * (w >> h)


def literal_even_predecessors(y: int):
    """Independent exhaustive integer predecessor calculation at a fixed y."""
    found = set()
    h, power3 = 0, 1
    while (y - 1) % power3 == 0:
        z = 1 + (1 << h) * ((y - 1) // power3)
        for a in range(1, z.bit_length()):
            x = 3 << a
            if section_next(x) == z and first_even(x) == y:
                found.add((x, h, a, "special"))
            m = (1 << (a + 1)) + 1
            u, remainder = divmod(2 * z - 2 * a + 1, m)
            if remainder == 0 and u >= 5 and u % 2 == 1:
                x = u << a
                if first_even(x) == y:
                    found.add((x, h, a, "generic"))
        h += 1
        power3 *= 3
    return sorted(found)


def child_node(node: tuple[int, int, int], h: int, a: int):
    s, b, d = node
    return (s + a + h + 1,
            (1 << (a + h + 1)) * (b - d) +
            (1 << a) * d * pow(3, h) * (3 - 2 * a),
            d * pow(3, h) * ((1 << (a + 1)) + 1))


def check_case(J, P, nodes, edges):
    assert P > 0 and J >= 100 and nodes[0] == (0, 0, 1)
    expected = {i: set() for i in range(len(nodes))}
    for parent, h, a, child in edges:
        assert 0 <= parent < len(nodes) and 0 <= child < len(nodes)
        assert a >= 1 and h >= 0 and parent < child
        assert child_node(nodes[parent], h, a) == nodes[child]
        expected[parent].add((h, a))
    # Separate indexed nodes for every j>=J: crossed affine differences
    # have a slope whose sign agrees with their exact value at the base.
    for i, j in combinations(range(len(nodes)), 2):
        si, bi, di = nodes[i]
        sj, bj, dj = nodes[j]
        slope = (1 << si) * dj - (1 << sj) * di
        offset = bi * dj - bj * di
        at_base = slope * (1 << J) + offset
        assert at_base != 0
        assert slope == 0 or (at_base > 0) == (slope > 0)
    low_rows, reps, max_order, specials = 0, 0, 0, 0
    for index, (s, b, d) in enumerate(nodes):
        assert d > 0 and d % 2 == 1 and b % 2 == 0
        n0 = (1 << (J + s)) + b
        assert n0 % d == 0
        y0 = n0 // d
        assert y0 > 10
        # Since P is a period modulo d, every indexed node is integral.
        assert pow(2, P, d) == 1 % d
        H = v3(y0 - 1) + 1
        # The 3-adic valuation of y(j)-1 is unchanged along j=J+P*k.
        high_mod = d * pow(3, H)
        assert (pow(2, J + s, high_mod) + b - d) % high_mod != 0
        assert pow(2, P, high_mod) == 1
        actual = set()
        for h in range(H):
            D = d * pow(3, h)
            C = (1 << h) * (b - d) + D
            S = s + h
            # Full special u=3 exclusion: exact 2^j-vs-affine gap,
            # proved persistent for all j>=J by monotonicity and slope.
            e = (3 * D).bit_length() - 1
            h_gap = e - S
            assert h_gap >= 0 and J >= h_gap + 1
            L = 3 * D - (1 << e)
            U = (1 << (e + 1)) - 3 * D
            assert L > 0 and U > 0
            assert L * (1 << J) > (1 << h_gap) * C
            assert U * (1 << J) > (1 << (h_gap + 1)) * (D * (J + 3) - C)
            assert U * (1 << J) >= (1 << (h_gap + 1)) * D
            specials += 1
            def K(a):
                return D * (2 * a - 1) - 2 * C
            # From a>=A, odd 1<K(a)<2^a implies generic impossibility
            # modulo 2^(a+1)+1. The three inequalities persist by induction.
            A = next(a for a in range(1, 100)
                     if 1 < K(a) < (1 << a) and (1 << a) >= 2 * D)
            assert K(A) % 2 == 1
            for a in range(1, A):
                m = D * ((1 << (a + 1)) + 1)
                order = order_two(m)
                assert pow(2, order, m) == 1
                q = order // gcd(order, P)
                assert pow(2, P * q, m) == 1
                low_rows += 1
                reps += q
                max_order = max(max_order, order)
                matched = []
                for k in range(q):
                    if pow(2, J + S + 1 + P * k, m) == K(a) % m:
                        matched.append(k)
                # The complete periodic test must agree with the DAG,
                # including every k for an intended branch.
                if (h, a) in expected[index]:
                    assert len(matched) == q, (J, index, h, a, q, matched)
                    actual.add((h, a))
                else:
                    assert matched == [], (J, index, h, a, q, matched)
        assert actual == expected[index], (J, index, actual, expected[index])
        # Independent fixed-exponent inverse, including exceptional cases.
        literal = literal_even_predecessors(y0)
        assert {(h, a) for _, h, a, typ in literal} == expected[index]
        assert all(typ == "generic" for _, _, _, typ in literal)
        for x, h, a, typ in literal:
            child = child_node((s, b, d), h, a)
            assert child in nodes
            s2, b2, d2 = child
            assert d2 * x == (1 << (J + s2)) + b2
            assert x > 10 and x < y0
    # Every declared edge is genuine for all k: its modular quotient is
    # integral for every k (above), and its parity is constant since the
    # change in numerator is divisible by twice the odd denominator.
    for parent, h, a, child in edges:
        s, b, d = nodes[parent]
        D = d * pow(3, h)
        C = (1 << h) * (b - d) + D
        S = s + h
        modulus = D * ((1 << (a + 1)) + 1)
        initial = (1 << (J + S + 1)) - (D * (2 * a - 1) - 2 * C)
        v0, remainder = divmod(initial, modulus)
        assert remainder == 0 and v0 >= 5 and v0 % 2 == 1
        assert pow(2, P, modulus) == 1
        assert ((1 << (J + S + 1)) * (pow(2, P, modulus) - 1)) % (2 * modulus) == 0
        for k in (0, 1):
            exponent = J + P * k
            xs, xb, xd = nodes[child]
            ys, yb, yd = nodes[parent]
            x = ((1 << (exponent + xs)) + xb) // xd
            y = ((1 << (exponent + ys)) + yb) // yd
            assert first_even(x) == y
            assert ((x & -x).bit_length() - 1) == a
            z = section_next(x)
            assert (((z - 1) & -(z - 1)).bit_length() - 1) == h
    return (low_rows, reps, max_order, specials)



def check_f_five_step_witness(j, valuations):
    """Prove an actual depth-five F inverse path at the base exponent."""
    y = 1 << j
    assert len(valuations) == 5
    for a in valuations:
        denominator = (1 << (a + 1)) + 1
        v, rem = divmod(2 * y - 2 * a + 1, denominator)
        assert rem == 0 and v >= 5 and v % 2 == 1
        x = (1 << a) * v
        assert x >= 5 and x < y and section_next(x) == y
        y = x



def run():
    for a, b in combinations(CASES, 2):
        assert (a[0] - b[0]) % gcd(a[1], b[1]) != 0
    for case in CASES:
        for r, p in PRIOR_E:
            assert (case[0] - r) % gcd(case[1], p) != 0
        rows, reps, largest, specials = check_case(*case)
        print(f"PASS j={case[0]}+{case[1]}k nodes={len(case[2])} "
              f"edges={len(case[3])} low-valuation checks={rows} "
              f"complete period representatives={reps} "
              f"largest period={largest} special-gap cases={specials}")
    for j, period, nodes, edges in CASES:
        check_f_five_step_witness(j, F_PATHS[j])
    refined_periods = tuple((j, lcm(period, 5400))
                            for j, period, nodes, edges in CASES)
    added_density = sum((Fraction(1, p) for j, p in refined_periods),
                        Fraction(0))
    assert added_density == Fraction(4111, 245381400)
    print("Refined disjoint from 3596/5400 F-depth-five classes:",
          refined_periods)
    print("Additional exponent-class density:", added_density)
    print("PASS: seven mutually disjoint new all-k E inverse-cone "
          "certificates, disjoint from nine prior E families.")


if __name__ == "__main__":
    run()
