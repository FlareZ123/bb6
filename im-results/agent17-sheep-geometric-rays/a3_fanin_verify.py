"""Exact independent tests for the Sheep valuation-three fan-in theorem."""

def v3(n: int) -> int:
    r = 0
    while n % 3 == 0:
        n //= 3
        r += 1
    return r


def e(x: int) -> tuple[int, int]:
    a = (x & -x).bit_length() - 1
    v = x >> a
    assert a >= 1 and v >= 3 and v % 2 == 1
    f = x + a + (3 if v == 3 else (v - 1) // 2)
    z = f - 1
    h = (z & -z).bit_length() - 1
    return 1 + 3**h * (z >> h), h


checked = 0
literal = 0
for k in range(1, 101):
    j = 4 * 3**k
    H = k + 1
    hs = list(range(1, H + 1, 16))
    assert len(hs) == k // 16 + 1
    for h in hs:
        d = 3**h
        assert pow(2, j, d) == 1
        assert pow(2, j, 17) == 16
        m = 17 * d
        assert (pow(2, j+h+1, m) - 2**(h+1) - 3**(h+1)) % m == 0
        checked += 1
        if k <= 6:
            Y = 1 << j
            q = (Y - 1) // d
            v, r = divmod(2**(h+1) * q - 3, 17)
            assert r == 0 and v >= 5 and v % 2 == 1
            assert e(8 * v) == (Y, h)
            literal += 1
    if k in (1, 2, 15, 16, 17, 31, 32, 64, 100):
        print(f"k={k}, j_digits={len(str(j))}, a=3 parents={len(hs)}, hidden_lengths={hs}")

for j in range(12, 30001, 8):
    H = 1 + v3(j)
    for h in range(1, H + 1, 16):
        mod = 17 * 3**h
        assert pow(2, j, 3**h) == 1
        assert (pow(2, j+h+1, mod) - 2**(h+1) - 3**(h+1)) % mod == 0
        checked += 1
print(f"PASS: {checked} exact modular family conditions, {literal} full literal F/E transitions.")
