"""Finite independent stress test for the P1 periodic inverse-word obstruction.

This enumerates bitmask words only up to the supplied cost bound.  The
all-cost theorem in README.md is a paper proof, not a conclusion of this test.
"""

from math import gcd


def multiplicative_order_two(denominator: int) -> int:
    """Order of 2 modulo an odd integer >= 3."""
    assert denominator >= 3 and denominator % 2 == 1
    residue = 2 % denominator
    order = 1
    while residue != 1:
        residue = (2 * residue) % denominator
        order += 1
    return order


def audit_word(cost: int, marker: int) -> tuple[int, int]:
    """Return the reduced denominator and binary repetend period."""
    modulus = (1 << cost) - 1
    denominator = modulus // gcd(modulus, marker)
    if denominator == 1:
        assert marker == modulus
        return denominator, 1
    period = multiplicative_order_two(denominator)
    assert 0 < period < denominator
    assert cost % period == 0
    lower = marker & ((1 << period) - 1)
    assert lower & (1 << (period - 1))
    assert lower * modulus == marker * ((1 << period) - 1)
    return denominator, period


def verify(max_cost: int = 21) -> dict[str, int]:
    checked = 0
    slope_integral = 0
    for cost in range(1, max_cost + 1):
        modulus = (1 << cost) - 1
        for low in range(1 << (cost - 1)):
            marker = (1 << (cost - 1)) | low
            if marker == modulus:
                continue  # all depth-zero transitions
            checked += 1
            if (marker * cost) % modulus:
                continue
            slope_integral += 1
            denominator, period = audit_word(cost, marker)
            assert denominator > period
            reduced_marker = marker & ((1 << period) - 1)
            assert (reduced_marker * period) % ((1 << period) - 1)
    return {
        "max_cost": max_cost,
        "nontrivial_marker_words_checked": checked,
        "integer_slope_candidate_words": slope_integral,
        "primitive_periodic_ray_candidates": 0,
    }


if __name__ == "__main__":
    print(verify())
