"""Uniform 3-adic, exceptional-source, and high-a generic premises."""
from independent_cones_data import node_value, v3


def check_bounds(j0, period, node):
    s, b, d = node
    assert d > 0 and d % 2 == 1
    assert pow(2, period, d) == 1 % d
    y0 = node_value(node, j0)
    assert y0 > 10 and y0 % 2 == 0
    hbound = v3(y0 - 1) + 1
    modulus = d * 3 ** hbound
    assert pow(2, period, modulus) == 1
    assert (pow(2, j0 + s, modulus) + b - d) % modulus != 0
    cutoffs = []
    for h in range(hbound):
        D = d * 3 ** h
        C = D + 2 ** h * (b - d)
        # Exceptional predecessor equation:
        # (3D)*2^a + D*a + (3D-C) = 2^(j+s+h).
        A = 3 * D
        ex_c = 3 * D - C
        assert ex_c > 0
        e = A.bit_length() - 1
        assert 2 ** e < A < 2 ** (e + 1)
        t0 = j0 + s + h - e - 1
        assert t0 >= 1
        L = 2 ** (e + 1) - A
        assert L * 2 ** t0 > D * t0 + ex_c
        assert L * 2 ** t0 > D
        # High-a generic nonresidue, extended inductively to all a>=cutoff.
        cutoff = 1
        while True:
            K = D * (2 * cutoff - 1) - 2 * C
            if 1 < K < 2 ** cutoff and K % 2 == 1 and 2 ** cutoff >= 2 * D:
                break
            cutoff += 1
            assert cutoff < 200
        cutoffs.append(cutoff)
    return cutoffs
