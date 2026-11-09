"""Exact periodic depth certificate for eight Sheep mixed inverse corridors.

Uses only modular arithmetic; never constructs astronomical Turing-machine tapes.
For all t>=0, the proof in README.md establishes one Hensel residue modulo
3^t for the divisibility test at precision 3^(10+t).
"""

from fractions import Fraction

BASE = 17496
DELTA = BASE * 63
Q = 10
# (residue, exponent offset, numerator additive term, denominator, 3-valuation)
FAMILIES = ((29, 10, 25220, 3483, 4),) + tuple(
    (r, 11, 680296, 59049, 10) for r in (8, 17, 26, 35, 44, 53, 62)
)


def numerator_mod(family: tuple[int, int, int, int, int], k: int, modulus: int) -> int:
    r, offset, c, _, _ = family
    return (pow(2, BASE * r + offset + DELTA * k, modulus) + c) % modulus


def lift(family: tuple[int, int, int, int, int], digits: int) -> int:
    """Unique k mod 3**digits with 3**(Q+digits) | numerator(k)."""
    k = 0
    period = 1
    for t in range(digits):
        modulus = 3 ** (Q + t + 1)
        choices = [k + u * period for u in range(3)
                   if numerator_mod(family, k + u * period, modulus) == 0]
        assert len(choices) == 1, (family[0], t, choices)
        k = choices[0]
        period *= 3
    assert numerator_mod(family, k, 3 ** (Q + digits)) == 0
    return k


def density_at_least(family: tuple[int, int, int, int, int], depth: int) -> Fraction:
    """Natural density in k>=0 with >=depth genuine P edges after terminal."""
    e = family[4]
    return Fraction(1, 3 ** max(0, e + 2 * depth - Q))


def run() -> None:
    assert DELTA == 1102248
    assert (pow(2, DELTA, 3 ** Q) - 1) % (3 ** Q) == 0
    assert (pow(2, DELTA, 3 ** (Q + 1)) - 1) % (3 ** (Q + 1)) != 0
    for f in FAMILIES:
        r, _, _, denominator, e = f
        assert numerator_mod(f, 0, denominator) == 0
        assert (pow(2, DELTA, denominator) - 1) % denominator == 0
        assert numerator_mod(f, 0, 3 ** Q) == 0
        assert denominator % (3 ** (e + 1)) != 0
        assert denominator % (3 ** e) == 0
        for t in range(9):
            k = lift(f, t)
            assert numerator_mod(f, k, 3 ** (Q + t)) == 0
            if t <= 5:
                period = 3 ** t
                # Verify the computed root is the *only* passing residue.
                hits = sum(numerator_mod(f, x, 3 ** (Q + t)) == 0
                           for x in range(period))
                assert hits == 1, (r, t, hits)
        print(f"r={r:2d} terminal h={3 if r==29 else 8}: "
              f"base L={max(0,(Q-e)//2)}, residues k(mod 9)="
              f"{lift(f, 2)}, density L>=4={density_at_least(f,4)}")

    for depth in range(0, 9):
        # n = r + 63*k, and eight r progressions are pairwise disjoint.
        total = sum((density_at_least(f, depth) for f in FAMILIES), Fraction()) / 63
        # Targets have a genuine inverse branch of at least depth+1 (terminal+P).
        print(f"P depth >= {depth}, root-path depth >= {depth+1}: "
              f"lower density among n = {total} ({float(total):.12%})")


if __name__ == "__main__":
    run()
