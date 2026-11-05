"""All-exponent integer certificate for coefficient rays with no Sheep E parent.

Python 3.10+, standard library only. The mathematical soundness argument is in README.md.
"""

COEFFICIENTS = (9, 21, 39, 81, 99, 111, 165, 171, 189, 201, 219, 225, 255, 291)


def high_cutoff(c: int) -> int:
    b = (c + 3) // 2
    while not (
        c < 2 * b - 1
        and 2 ** (b + 1) + 1 > c * (c + 2 * b - 1) + (2 * b - 1)
    ):
        b += 1
    return b


def section_step(x: int) -> int:
    a = (x & -x).bit_length() - 1
    u = x >> a
    assert a >= 1 and u >= 3 and (u & 1)
    return x + a + (3 if u == 3 else (u - 1) // 2)


def even_successor(x: int) -> int:
    z = section_step(x)
    v = z - 1
    h = (v & -v).bit_length() - 1
    return 1 + 3**h * (v >> h)


def exact_even_parents(y: int) -> list[int]:
    """Enumerate all source valuations in a finite exact target, independently of the sieve."""
    found = []
    for a in range(1, y.bit_length() + 2):
        x = 3 << a
        if x < y and section_step(x) == y and even_successor(x) == y:
            found.append(x)
        m = (1 << (a + 1)) + 1
        v, rem = divmod(2 * y - 2 * a + 1, m)
        if rem == 0 and v >= 5 and v % 2:
            x = v << a
            if x < y and section_step(x) == y and even_successor(x) == y:
                found.append(x)
    return found


def certify(c: int) -> tuple[int, int]:
    assert c >= 9 and c % 6 == 3
    d = (c // 3).bit_length() - 1
    delta = c - 3 * (1 << d)
    assert 0 < delta and c < 3 * (1 << (d + 1))
    assert d + 5 < 4 * delta, "special-source all-exponent gap at n=2"

    b0 = high_cutoff(c)
    k0 = 2 * b0 - 1
    m0 = (1 << (b0 + 1)) + 1
    assert c < k0 and m0 > c * (c + k0) + k0
    # Both high-valuation inequalities persist at b+1 by the written induction.
    assert m0 > 2 * (c + 1) + 1
    rows = 0
    for a in range(1, b0):
        m = (1 << (a + 1)) + 1
        k = 2 * a - 1
        assert pow(4, a + 1, m) == 1
        residue = 2 * c % m
        for j in range(a + 1):
            assert residue != k % m, ("counterexample", c, a, j, m)
            residue = 4 * residue % m
            rows += 1
        assert residue == 2 * c % m

    for j in range(1, 21):
        y = c << (2 * j)
        assert not exact_even_parents(y), (c, j, exact_even_parents(y))
    return b0, rows


def main() -> None:
    total = 0
    for c in COEFFICIENTS:
        b, rows = certify(c)
        total += rows
        print(f"PASS c={c:3d}, b>={b:3d} high gap, {rows:5d} complete low-b modular checks")
    assert section_step(1382) == 1728 and even_successor(1382) == 1728
    assert 27 * 4**3 == 1728
    print(f"PASS negative control: E(1382)=27*4^3=1728; coefficient 27 is not certified")
    print(f"COMPLETE {len(COEFFICIENTS)} all-k rays, {total} modular tests, 280 direct parent scans")


if __name__ == "__main__":
    main()
