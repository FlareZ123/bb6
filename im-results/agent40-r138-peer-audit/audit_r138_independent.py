"""Independent exact-arithmetic audit of Agent14's Sheep r=138 child proof.

Reproduces the child congruence obstructions and tests source-shaped
even-return equations. Python standard library only. Independent finite
validation, not a replacement for the source-connected Lean theorem.

Run: python audit_r138_independent.py
"""
from math import gcd

CHILDREN = (
    ("child1", 15, 2, 141, (8, 10, 12, 14)),
    ("child2", 81, 68, 143, (11, 13)),
)
STRIDE = 4860


def order_two(modulus):
    """The smallest positive p with 2**p == 1 modulo an odd modulus."""
    assert modulus > 1 and modulus % 2
    value, period = 2 % modulus, 1
    while value != 1:
        value = value * 2 % modulus
        period += 1
    return period


def even_successor(x):
    """First-even Sheep section return for a nonterminal even x."""
    assert x >= 6 and x % 2 == 0
    a = (x & -x).bit_length() - 1
    v = x >> a
    assert v >= 3 and v % 2 == 1
    z = x + a + (3 if v == 3 else (v - 1) // 2)
    h = ((z - 1) & -(z - 1)).bit_length() - 1
    u = (z - 1) >> h
    y = 1 + 3**h * u
    assert u % 2 == 1 and y % 2 == 0
    return a, v, h, u, z, y


def audit_source_algebra():
    """Test generic and exceptional predecessor identities independently."""
    tested = 0
    for a in range(1, 12):
        for v in range(3, 256, 2):
            x = (2**a) * v
            aa, vv, h, u, z, y = even_successor(x)
            assert (aa, vv) == (a, v)
            assert z - 1 == 2**h * u
            for _, d, c, _, _ in CHILDREN:
                D = d * 3**h
                if v == 3:
                    assert (
                        D * (3 * 2**a + a + 2) + 2**h * (d + c)
                        == 2**h * (d * y + c)
                    )
                else:
                    T = D * (2**(a + 1) + 1)
                    B = (2 * a - 3) * D + 2**(h + 1) * (d + c)
                    assert T * v + B == 2**(h + 1) * (d * y + c)
                tested += 1
    return tested


def audit_residue_certificates():
    """Independently check 62 cases and 221 exponent-period representatives."""
    cases, reps, max_period, negative_B = 0, 0, 0, 0
    for name, d, c, n0, limits in CHILDREN:
        for h, stop_a in enumerate(limits):
            for a in range(1, stop_a):
                D = d * 3**h
                T = D * (2**(a + 1) + 1)
                B = (2 * a - 3) * D + 2**(h + 1) * (d + c)
                C = 2 * T - B if B >= 0 else -B
                negative_B += int(B < 0)
                p = order_two(T)
                q = p // gcd(p, STRIDE)
                assert pow(2, p, T) == 1
                assert (STRIDE * q) % p == 0
                root = n0 + h + 1
                residues = {
                    (pow(2, root + STRIDE * k, 2 * T) + C) % (2 * T)
                    for k in range(q)
                }
                assert T not in residues, (name, h, a, T, p, q)
                for k in range(q):
                    e = root + STRIDE * k
                    assert pow(2, e + p, 2 * T) == pow(2, e, 2 * T)
                    assert (
                        pow(2, e + STRIDE * q, 2 * T)
                        == pow(2, e, 2 * T)
                    )
                cases += 1
                reps += q
                max_period = max(max_period, p)
    assert cases == 62 and reps == 221
    return cases, reps, max_period, negative_B


def audit_high_h():
    assert pow(2, 141, 1215) == 827
    assert pow(2, 324, 1215) == 1
    assert pow(2, 143, 729) == 635
    assert pow(2, 486, 729) == 1
    assert STRIDE % 324 == 0 and STRIDE % 486 == 0



def audit_generic_high_cutoffs():
    """Verify the six signed-gap induction bases, not a bounded-a sweep."""
    rows = []
    for name, d, c, _, limits in CHILDREN:
        for h, start_a in enumerate(limits):
            D = d * 3**h
            K = (2 * start_a - 3) * D + 2**(h + 1) * (d + c)
            assert K % 2 == 1 and 1 < K < 2**start_a
            assert 2 * D < 2**start_a
            # For a>=start_a, K(a+1)=K(a)+2D and 2D<2**a.
            # Induction gives 1<K(a)<2**a for every larger a.
            rows.append((name, h, start_a, D, K))
    assert len(rows) == 6
    return rows


def audit_special_sandwich():
    """Construct six exponential-vs-linear interval proofs."""
    rows = []
    for name, d, c, n0, limits in CHILDREN:
        for h in range(len(limits)):
            D = d * 3**h
            coeff, slope, offset = 3*D, D, 2*D + 2**h * (d + c)
            t = coeff.bit_length()-1
            gap = 2**(t+1)-coeff
            start_a = 1
            while slope*start_a+offset >= gap*2**start_a:
                start_a += 1
            assert coeff > 2**t
            assert slope*start_a+offset < gap*2**start_a
            assert slope*start_a+offset > slope
            assert all(
                coeff*2**a+slope*a+offset < 2**n0
                for a in range(1,start_a)
            )
            # At all a>=start_a, the expression is strictly between
            # 2**(a+t) and 2**(a+t+1): the upper inequality persists
            # because slope*a+offset>slope, so g(a+1)<2*g(a).
            # At smaller a it is below 2**n0 and cannot equal
            # the required power with exponent n0+4860*k+h.
            rows.append((name,h,coeff,slope,offset,t,start_a))
    assert len(rows) == 6
    return rows


def main():
    n = audit_source_algebra()
    cases, reps, max_period, negative_B = audit_residue_certificates()
    audit_high_h()
    cutoffs = audit_generic_high_cutoffs()
    sandwiches = audit_special_sandwich()
    print("PASS: independent even-return algebra identities:", n)
    print("PASS: all child-branch modular obstructions:", cases)
    print("PASS: all exponent-period representatives:", reps)
    print("PASS: maximum reconstructed period:", max_period)
    print("PASS: negative-B branches handled:", negative_B)
    print("PASS: both high-h base congruence obstructions")
    print("PASS: six universal generic high-a induction cutoffs:", [r[2] for r in cutoffs])
    print("PASS: six universal special-branch power sandwiches:", [r[-1] for r in sandwiches])
    print("LIMIT: arithmetic audit only; all-k high-a and Lean import not repeated")


if __name__ == "__main__":
    main()
