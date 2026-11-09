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
        print(f"P-depth parity={parity}: forbidden a = {count}/{PERIOD} = {density}")


if __name__ == "__main__":
    run()
