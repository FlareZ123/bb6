"""Independent finite checks for Agent 16's Sheep Machine predecessor theorem.

The infinite assertions are proved by arithmetic in README.md; this script
is deliberately bounded testing, and never purports to certify all exponents.
"""

ODD_BLOCK = {19, 23, 35, 43, 47, 55, 59}
EVEN_BLOCK = {8, 16, 40, 56, 64}


def section_map(t: int) -> int | None:
    assert t >= 3
    a = (t & -t).bit_length() - 1
    u = t >> a
    if u == 1:
        return None
    if u == 3:
        return t + a + 3
    return t + a + (u - 1) // 2


def two_counter_step(m: int, k: int) -> tuple[int, int] | None:
    assert m >= 0 and k >= 0
    if m == 0:
        return (0, 2) if k == 0 else (2, k - 1)
    if m == 1:
        return None
    if m % 2 == 0:
        return (3 * (m // 2) + k, 1)
    r = (m - 3) // 2
    return (r, r + k + 4)


def two_counter_section(t: int) -> int | None:
    m, k = t - 3, 1
    for _ in range(2 * t.bit_length() + 12):
        s = two_counter_step(m, k)
        if s is None:
            return None
        m, k = s
        if k == 1:
            return m + 3
    raise AssertionError(("No return", t))


def inverse(y: int) -> tuple[int, ...]:
    """Exhaust all possible valuations of F's predecessors of positive y."""
    assert y >= 1
    parents: set[int] = set()
    for a in range(y.bit_length() + 1):
        special = 3 << a
        if section_map(special) == y:
            parents.add(special)
        numerator = 2 * y - 2 * a + 1
        modulus = (1 << (a + 1)) + 1
        u, rem = divmod(numerator, modulus)
        if rem == 0 and u >= 5 and u % 2 == 1:
            source = u << a
            assert section_map(source) == y
            parents.add(source)
    return tuple(sorted(parents))


def power_parent(j: int) -> int | None:
    if j >= 4 and j % 2 == 0:
        return ((1 << (j + 1)) + 1) // 3
    if j >= 7 and j % 4 == 3:
        return 2 * (((1 << (j + 1)) - 1) // 5)
    return None


def order_of_two(modulus: int) -> int:
    r = 2 % modulus
    for k in range(1, 1000):
        if r == 1:
            return k
        r = (r * 2) % modulus
    raise AssertionError(modulus)


def modulus_rows(multiplier: int, linear: int, offset: int,
                 rows: dict[int, tuple[int, int | None]]) -> None:
    for a, (expected_period, expected_j) in rows.items():
        modulus = multiplier * ((1 << (a + 1)) + 1)
        period = order_of_two(modulus)
        assert period == expected_period, (a, modulus, period)
        candidates = [
            j for j in range(period)
            if pow(2, j + offset, modulus) == (linear * a - (linear - 1)) % modulus
        ]
        assert candidates == ([] if expected_j is None else [expected_j]), (
            a, modulus, candidates
        )


def main() -> None:
    for t in range(3, 100_003):
        assert section_map(t) == two_counter_section(t), t
    print("PASS 100,000 exact comparisons against independent two-counter section")

    for j in range(256):
        expected = power_parent(j)
        assert inverse(1 << j) == (() if expected is None else (expected,)), j
    print("PASS 256 complete direct-inverse checks for halting powers")

    for j in range(7, 1207, 4):
        t = power_parent(j)
        assert t is not None
        parents = inverse(t)
        if j % 60 in ODD_BLOCK or j == 7:
            assert not parents, (j, parents)
        else:
            assert parents, j
    for j in range(4, 1206, 2):
        t = power_parent(j)
        assert t is not None
        parents = inverse(t)
        if j % 72 in EVEN_BLOCK or j == 4:
            assert not parents, (j, parents)
        else:
            assert parents, j
    print("PASS 901 exact second-generation inverse checks")

    # Odd j=3(mod4): 2^(j+3) == 10*a-1 modulo 5*(2^(a+1)+1).
    odd_rows = {
        0: (4, None), 1: (20, 11), 2: (12, 3),
        3: (8, None), 4: (20, None), 5: (60, 7), 6: (28, None),
    }
    # Even j: 2^(j+2) == 6*a-5 modulo 3*(2^(a+1)+1).
    even_rows = {
        0: (6, 0), 1: (4, 2), 2: (18, 14),
        3: (8, 4), 4: (30, None),
    }
    # Here offset is 3 or 2, and target residues are 10*a-1 or 6*a-5.
    # The helper expects linear*a-(linear-1), so set explicit checks below.
    for multiplier, slope, constant, offset, rows in (
        (5, 10, 1, 3, odd_rows), (3, 6, 5, 2, even_rows)
    ):
        for a, (period, expected_j) in rows.items():
            modulus = multiplier * ((1 << (a + 1)) + 1)
            assert order_of_two(modulus) == period
            hits = [j for j in range(period)
                    if pow(2, j + offset, modulus) == (slope * a - constant) % modulus]
            assert hits == ([] if expected_j is None else [expected_j]), (
                multiplier, a, hits
            )
    for j in range(7, 12007, 4):
        allowed = [a for a, n, r in ((1, 20, 11), (2, 12, 3), (5, 60, 7))
                   if j % n == r]
        actual = [a for a in range(7)
                  if pow(2, j + 3, 5 * ((1 << (a + 1)) + 1))
                  == (10*a - 1) % (5 * ((1 << (a + 1)) + 1))]
        assert actual == allowed, (j, actual, allowed)
    for j in range(4, 12006, 2):
        allowed = [a for a, n, r in ((0, 6, 0), (1, 4, 2),
                   (2, 18, 14), (3, 8, 4)) if j % n == r]
        actual = [a for a in range(5)
                  if pow(2, j + 2, 3 * ((1 << (a + 1)) + 1))
                  == (6*a - 5) % (3 * ((1 << (a + 1)) + 1))]
        assert actual == allowed, (j, actual, allowed)
    print("PASS 12 complete modular cycles and 9,000 additional residue checks")

    t = 5
    for step in range(100_000):
        assert t.bit_count() != 1, ("power reached", step, t)
        t = section_map(t)
        assert t is not None
    print("PASS 100,000 actual section steps without halting")
    print("Final section: bits =", t.bit_length(), ", mod 1,000,000,007 =", t % 1_000_000_007)


if __name__ == "__main__":
    main()
