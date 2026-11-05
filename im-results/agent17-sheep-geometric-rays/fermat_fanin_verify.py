"""Exact modular certificates for four Sheep power-gate fan-in sectors."""

ROWS = (
    (1, 1, 2, 1, 1),
    (2, 3, 16, 1, 1),
    (3, 7, 256, 92, 91),
    (4, 15, 65536, 43005, 43004),
)


def even_step(x: int) -> tuple[int, int]:
    a = (x & -x).bit_length() - 1
    v = x >> a
    assert a >= 1 and v >= 3 and v & 1
    f = x + a + (3 if v == 3 else (v - 1) // 2)
    z = f - 1
    h = (z & -z).bit_length() - 1
    return 1 + 3**h * (z >> h), h


for r, a, period, first, min_k in ROWS:
    m = 2**(a+1) + 1
    c = 2*a - 3
    g = 3*pow(2, -1, m) % m
    R = (-4*pow(c, -1, m)) % m
    assert pow(2, 2**r, m) == m-1
    assert pow(g, period, m) == 1
    assert pow(g, period//2, m) != 1
    assert pow(g, first, m) == R
    assert pow(3, period, m) == pow(2, period, m)
    for k in (min_k, min_k + 1, min_k + period, min_k + 2*period):
        hs = range(first, k+2, period)
        count = max(0, (k+1-first)//period+1)
        assert len(hs) == count
        for h in hs:
            assert pow(g, h, m) == R
            inv3h = pow(pow(3, h, m), -1, m)
            q_mod = (-2 * inv3h) % m
            assert (pow(2, h+1, m)*q_mod - c) % m == 0
        print(f"a={a:2}, k={k:6}, h-first={first:5}, direct-parents>={count}")
    if r in (1, 2):
        for k in range(1, 7):
            j = 2**r * 3**k
            for h in range(first, k+2, period):
                y = 1 << j
                q, rem = divmod(y-1, 3**h)
                assert rem == 0 and q & 1
                v, rem = divmod(2**(h+1)*q-c, m)
                assert rem == 0 and v >= 5 and v & 1
                assert even_step(2**a*v) == (y, h)
print("PASS: four modular periods, lattice arithmetic and all practicable literal edges")
