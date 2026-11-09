"""All-index Sheep E inverse chains into 2^(17496*n), with exact modular periods.

Imports the existing s=0 root sieve. Full inverse-row periods validate exact
affine-parent chains and prove new all-k and selected-phase exclusions.
"""
from stratum_certificate import SCALE, certify_stratum

Z = (10, -16576, 3483)
T = (13, -174404, 31347)
U = (16, -1771396, 282123)
X = (11, -28292, 59049)
FULL_Z = (1, 8, 22, 43, 50)
FULL_EXCLUDED = (1, 22, 43, 50)
X_ROWS = (8, 17, 35, 44, 62)
X_GOOD_PHASES = {
    8: (0, 1, 3, 4, 7),
    17: (0, 3, 5, 6, 8),
    35: (0, 1, 4, 6, 7),
    44: (0, 2, 3, 5, 6),
    62: (1, 3, 4, 6, 7),
}


def gap_threshold_node(d, b):
    for a in range(1, 100):
        k = d * (2*a-1) - 2*b
        if 1 < k < 2**a and 2**a >= 2*d:
            return a
    raise AssertionError((d, b))


def order_delta(m, delta):
    v = 1
    step = pow(2, delta, m)
    for q in range(1, 2000):
        v = v * step % m
        if v == 1:
            return q
    raise AssertionError((m, delta))


def v3(d):
    s = 0
    while d % 3 == 0:
        s += 1
        d //= 3
    return s


def uniform_hidden_h0(node, r, phase=0, period=1):
    s, b, d = node
    modulus = 3 ** (v3(d) + 1)
    # When d*y = 2^(j+s)+b, h>=1 requires 3^(v3(d)+1)
    # to divide 2^(j+s)+b-d. Check its uniform negation.
    exp0 = SCALE*(r + 63*phase)+s
    delta = SCALE*63*period
    assert pow(2, delta, modulus) == 1
    assert (pow(2, exp0, modulus)+b-d) % modulus != 0


def low_parent_pairs(node, r, phase=0, period=1):
    s, b, d = node
    # For hidden h=0, the exact generic source equation is
    # 2^(j+s+1) = d*(2^(a+1)+1)*v + d*(2*a-1) - 2*b.
    delta = SCALE*63*period
    j0 = SCALE*(r+63*phase)
    remaining = []
    total_rows = 0
    for a in range(1, gap_threshold_node(d, b)):
        modulus = d*(2**(a+1)+1)
        residue = d*(2*a-1)-2*b
        q = order_delta(modulus, delta)
        hits = [k for k in range(q) if
                pow(2, j0+s+1+delta*k, modulus) == residue % modulus]
        total_rows += 1
        if hits:
            remaining.append((a, q, tuple(hits)))
    # Higher a: existing source-independent Lean odd-power gap.
    # Special source: 3*d*2^a+d*(a+3)-b=2^(j+s);
    # a>=100 gives an open power-free interval; a<100 gives <2^121.
    assert 0 < d*103-b < 2**100
    assert d < 2**100
    assert 3*d*2**99+d*102-b < 2**121
    assert 121 < SCALE
    return remaining, total_rows


def main():
    root_rows, free, active = certify_stratum(0)
    assert set(FULL_EXCLUDED).isdisjoint(free)
    assert set(X_ROWS).isdisjoint(free)
    for r in FULL_Z:
        assert (3, 6) in active[r]
        assert set(active[r]) <= {(3, 6), (8, 2)}
        for node in (Z, T, U):
            uniform_hidden_h0(node, r)
        for node in (Z, T):
            live, count = low_parent_pairs(node, r)
            assert live == [(2, 1, (0,))], (node, r, live)
        leaf, count = low_parent_pairs(U, r)
        assert leaf == [], (r, leaf)
        print("Root Z->T->U branch terminates for all k at r=", r,
              "(U low generic rows=", count, ")")
    for r in X_ROWS:
        assert (8, 2) in active[r]
        assert set(active[r]) <= {(3, 6), (8, 2)}
        good = []
        for phase in range(9):
            modulus = 3 ** (v3(X[2]) + 1)
            exp = SCALE*(r+63*phase)+X[0]
            if (pow(2, exp, modulus)+X[1]-X[2]) % modulus:
                uniform_hidden_h0(X, r, phase, 9)
                live, count = low_parent_pairs(X, r, phase, 9)
                if not live:
                    good.append(phase)
        assert tuple(good) == X_GOOD_PHASES[r], (r, good)
        print("Root X branch terminates at r=",r," k mod 9 in",tuple(good))
    print("PASS: four whole r-progressions plus five 5/9-phase progressions")


if __name__ == "__main__":
    main()
