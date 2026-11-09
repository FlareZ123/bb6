"""Exact finite-period arithmetic audit of r29 all-depth side-exit exclusions."""

from fractions import Fraction
from math import lcm

PERIOD = lcm(20, 156, 136)


def excludes(a: int, depth_parity: int) -> bool:
    allowed17 = 67 if depth_parity == 0 else 131
    return (a % 20 == 1 or a % 156 == 125 or
            (a % 8 == 3 and a % 136 != allowed17))


def run() -> None:
    assert PERIOD == 26520
    for a in range(PERIOD):
        for q, residue, span in ((5, 1, 20), (13, 125, 156), (17, 99, 136)):
            assert ((2 ** (a + 1) + 1) % q == 0 and
                    (2 * a + 23) % q == 0) == (a % span == residue)
    for parity in (0, 1):
        count = sum(excludes(a, parity) for a in range(PERIOD))
        assert count == 4582
        density = Fraction(count, PERIOD)
        assert density == Fraction(2291, 13260)
        print(f"Z P-depth parity={parity}: forbidden a = {count}/{PERIOD} = {density}")
        interior_count = sum(
            excludes(a, parity) or a % 6 in (0, 4)
            for a in range(PERIOD)
        )
        assert Fraction(interior_count, PERIOD) == Fraction(2237, 4420)
        print(f"Z interior: forbidden generic a = {interior_count}/{PERIOD} = 2237/4420")
    period_x = lcm(20, 136)
    for parity in (0, 1):
        allowed_x = 35 if parity == 0 else 27
        count_x = sum(
            (a % 20 == 1 or (a % 8 == 3 and a % 136 != allowed_x))
            for a in range(period_x)
        )
        assert count_x == 114
        assert Fraction(count_x, period_x) == Fraction(57, 340)
        print(f"X P-depth parity={parity}: forbidden a = {count_x}/{period_x} = 57/340")
        period_int_x = lcm(period_x, 6)
        count_int_x = sum(
            (a % 20 == 1 or
             (a % 8 == 3 and a % 136 != allowed_x) or
             a % 6 in (0, 4))
            for a in range(period_int_x)
        )
        assert Fraction(count_int_x, period_int_x) == Fraction(511, 1020)
        print(f"X interior: forbidden generic a = {count_int_x}/{period_int_x} = 511/1020")


if __name__ == "__main__":
    run()
