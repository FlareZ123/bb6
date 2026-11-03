"""Exact check of coherent Sheep one-valuation corridors into halting powers.

All starting sections are synthetic. This does not inspect blank reachability.
"""

def step(t: int) -> int | None:
    if t < 5:
        raise ValueError("not a valid section")
    a = (t & -t).bit_length() - 1
    u = t >> a
    if u == 1:
        return None
    return t + a + (3 if u == 3 else (u - 1) // 2)


def first_even(t: int) -> int | None:
    z = step(t)
    if z is None:
        return None
    p = z - 1
    h = (p & -p).bit_length() - 1
    return 1 + (3 ** h) * (p >> h)


def family(i: int, k: int, v: int) -> int:
    return 2 * ((5 ** i) * (4 ** k) * v - 1)


def check() -> None:
    count = 0
    for length in range(1, 7):
        exponent = 6 * (5 ** (length - 1))
        numerator = (1 << exponent) + 1
        divisor = 5 ** length
        v, remainder = divmod(numerator, divisor)
        assert remainder == 0 and v >= 5 and v & 1 == 1
        t = family(0, length, v)
        for i in range(length):
            expected = family(i + 1, length - i - 1, v)
            assert t % 4 == 2 and t >= 6
            assert step(t) == expected
            assert first_even(t) == expected
            t = expected
            count += 1
        assert t == (1 << (exponent + 1))
        assert step(t) is None and t % 4 == 0
        print(f"L={length}: {length} exact first-even returns; terminal 2^{exponent+1}; "
              f"start width {family(0, length, v).bit_length()} bits")
    assert count == 21
    for length in range(1, 9):
        for odd_v in (5, 7, 13, 17, 123):
            t = family(0, length, odd_v)
            for i in range(length):
                expected = family(i + 1, length - i - 1, odd_v)
                assert t % 4 == 2
                assert first_even(t) == expected
                t = expected
            assert t % 4 == 0
    print("PASS: 21 halting-corridor links plus 360 arbitrary odd-seed links")


if __name__ == "__main__":
    check()
