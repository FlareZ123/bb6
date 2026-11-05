"""Exact finite audit of Agent17's h=3 even power-parent theorem.

Python 3.11+ standard library. The all-exponent theorem is proved
separately in POWER-PARENTS-H3.md, not by the finite test range.
"""

PERIODS = {
    1: (135, -11, 36, [22]),
    2: (243, 43, 162, [130]),
    3: (459, 97, 72, []),
    4: (891, 151, 270, []),
    5: (1755, 205, 36, []),
    6: (3483, 259, 378, [112]),
    7: (6939, 313, 144, []),
    8: (13851, 367, 486, []),
}

def f_source(x):
    a = (x & -x).bit_length() - 1
    v = x >> a
    if v < 3:
        return None
    return x + a + (3 if v == 3 else (v - 1) // 2)

def e_source(x):
    f = f_source(x)
    if f is None:
        return None
    h = ((f - 1) & -(f - 1)).bit_length() - 1
    return 1 + 3**h * ((f - 1) >> h)

def exhaustive_inverse(j):
    target = 1 << j
    all_sources = set()
    d = target - 1
    h = 0
    while d % (3**h) == 0:
        f = 1 + (1 << h) * (d // (3**h))
        for a in range(1, j + 1):
            modulus = (1 << (a + 1)) + 1
            numerator = 2*f - 2*a + 1
            v, remainder = divmod(numerator, modulus)
            if remainder == 0 and v >= 5 and v % 2 == 1:
                x = (1 << a) * v
                assert e_source(x) == target
                all_sources.add(x)
            x = 3 << a
            if f_source(x) == f and e_source(x) == target:
                all_sources.add(x)
        h += 1
    return all_sources

def formulas(j):
    assert j >= 18 and j % 18 == 0 and j % 54 != 0
    result = set()
    if j % 4 == 2:
        result.add(2 * ((1 << (j + 2)) - 1) // 15)
    if j % 8 == 4:
        result.add(8 * ((1 << (j + 2)) - 13) // 51)
    if j % 36 == 18:
        result.add(2 * ((1 << (j + 4)) + 11) // 135)
    if j % 162 == 126:
        result.add(4 * ((1 << (j + 4)) - 43) // 243)
    return result

def main():
    for a, (modulus, target, period, expected) in PERIODS.items():
        assert modulus == 27 * ((1 << (a + 1)) + 1)
        assert target == 54*a - 65
        assert pow(2, period, modulus) == 1
        hits = [n for n in range(period)
                if pow(2, n, modulus) == target % modulus]
        assert hits == expected, (a, hits, expected)
    print("All eight exact h=3 modular periods PASS")

    for a in range(9, 3000):
        assert 1 < 54*a-65 < (1 << a)
    print("High-a growth sanity PASS through a=2999")

    checked = 0
    for j in range(18, 1801, 18):
        if j % 54 == 0:
            continue
        actual = exhaustive_inverse(j)
        expected = formulas(j)
        assert actual == expected, (j, actual, expected)
        checked += 1
    print(f"Full first-even inverse equality PASS for {checked} exponents j<=1800")
    for j in (18, 36, 72, 126, 144, 180):
        if j % 54 != 0:
            print(f"j={j}: incoming valuation multiset = "
                  f"{[(x & -x).bit_length() - 1 for x in sorted(formulas(j))]}")

if __name__ == "__main__":
    main()
