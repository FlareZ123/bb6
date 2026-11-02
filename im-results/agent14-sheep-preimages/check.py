"""Exact arithmetic validation of the Sheep Machine preimage classification.

The proof of the universal bound on source valuation is given in README.md;
this program supplies independent finite checks only, not a substitute for it.
"""


def sheep(n: int) -> int | None:
    assert n >= 3
    a = (n & -n).bit_length() - 1
    u = n >> a
    if u == 1:
        return None
    if u == 3:
        return n + a + 3
    return n + a + (u - 1) // 2


def counter(m: int, k: int) -> tuple[int, int] | None:
    if m == 0:
        return (0, 2) if k == 0 else (2, k - 1)
    if m == 1:
        return None
    if m % 2 == 0:
        return (3 * (m // 2) + k, 1)
    return ((m - 3) // 2, (m - 3) // 2 + k + 4)


def section(t: int) -> int | None:
    m, k = t - 3, 1
    for i in range(2 * t.bit_length() + 10):
        s = counter(m, k)
        if s is None:
            return None
        m, k = s
        if k == 1:
            return m + 3
    raise AssertionError(f"No return to section for t={t}")


def predicted_parents(j: int) -> list[int]:
    if j == 1:
        return [3]
    if j < 2:
        return []
    y = 3 << j
    out = []
    for a in (1, 2, 3):
        u, r = divmod(2 * y - 2 * a + 1, (1 << (a + 1)) + 1)
        if r == 0 and u >= 5 and u % 2:
            out.append(u << a)
    return sorted(out)


def all_parents(j: int) -> list[int]:
    y = 3 << j
    out = []
    if y == 6:
        out.append(3)
    if (2 * y + 1) % 3 == 0:
        n = (2 * y + 1) // 3
        if n >= 5 and n & 1:
            out.append(n)
    for a in range(1, j + 2):
        if 3 * (1 << a) + a + 3 == y:
            out.append(3 << a)
        u, r = divmod(2 * y - 2 * a + 1, (1 << (a + 1)) + 1)
        if r == 0 and u >= 5 and u & 1:
            out.append(u << a)
    return sorted(set(out))


def main() -> None:
    for n in range(3, 200_000):
        assert sheep(n) == section(n), (n, sheep(n), section(n))
    for j in range(80):
        expected = predicted_parents(j)
        actual = all_parents(j)
        assert actual == expected, (j, actual, expected)
        assert all(sheep(n) == 3 << j for n in actual)
        if j >= 2 and j % 4 == 2:
            assert actual == []
    for j in range(2, 1601, 4):
        assert not all_parents(j), j
    x = 5
    for step in range(20_000):
        assert x != 0 and x & (x - 1) != 0
        assert x != 3 << (((x // 3).bit_length() - 1) if x % 3 == 0 else 0) or x % 3 != 0
        x = sheep(x)
        assert x is not None, step
    print("PASS: 199997 section comparisons, 80 complete inverse classifications,")
    print("400 higher-exponent no-predecessor checks, 20000 surviving actual-section steps.")
    print("last section state: bit_length=", x.bit_length(), "last_mod_1e9=", x % 1_000_000_000)


if __name__ == "__main__":
    main()
