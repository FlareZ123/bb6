"""Finite, exact arithmetic for source P1 inverse-depth word blocks.

All functions are pure and use only Python integer arithmetic. This code
generates candidates and finite modular certificates; theorems in
BlockPotential.lean and BlockSecondary.lean carry the mathematical proof.

The returned modulus checks are sufficient conditions, not an assertion
that an arbitrary word can occur from the genuine blank-root P1 orbit.
"""
from dataclasses import dataclass
from math import gcd
from typing import Sequence


@dataclass(frozen=True)
class WordBlock:
    depths: tuple[int, ...]
    total_cost: int
    scale: int
    slope: int
    constant: int
    certificate: str


def _certificate(scale: int, slope: int, cost: int, constant: int) -> str:
    modulus = scale - 1
    if (slope * cost) % modulus:
        return "primary"
    c = slope * cost // modulus
    g = gcd(slope, modulus)
    if (scale * c - constant) % g:
        return "secondary"
    return "inconclusive"


def analyze_word(depths: Sequence[int]) -> WordBlock:
    """Compute A,H,S,D for A*z'=z+H*(L+m)+D, m'=m+S.

    Every exact inverse edge of depth t contributes cost s=t+1. Its
    scaled equation is 2^s*z'=z+2^t*(L+m+t-1).
    """
    ds = tuple(depths)
    if not ds or any(t < 0 for t in ds):
        raise ValueError("A nonempty word of nonnegative depths is required")
    cost = slope = constant = 0
    for t in ds:
        exponent = cost + t
        bit = 1 << exponent
        slope += bit
        constant += bit * (exponent - 1)
        cost += t + 1
    scale = 1 << cost
    return WordBlock(
        ds, cost, scale, slope, constant,
        _certificate(scale, slope, cost, constant),
    )


def depths_from_bitmask(cost: int, slope: int) -> tuple[int, ...]:
    """Recover the unique inverse-depth word from its end-position bits."""
    if cost < 1 or not (1 << (cost - 1) <= slope < 1 << cost):
        raise ValueError("Slope needs its highest bit at total-cost position")
    previous_end = -1
    depths = []
    for position in range(cost):
        if slope & (1 << position):
            depths.append(position - previous_end - 1)
            previous_end = position
    return tuple(depths)


def nontrivial_unresolved_words(max_cost: int) -> list[WordBlock]:
    """Enumerate exactly the modularly inconclusive nonzero-depth words.

    Exhaustive over all depth words with total cost 1..max_cost, but uses
    the necessary primary divisibility to avoid exponential enumeration.
    A return of [] is finite computational evidence, not an all-cost
    theorem and not a statement of source reachability.
    """
    if max_cost < 1:
        raise ValueError("max_cost must be positive")
    unresolved = []
    for cost in range(1, max_cost + 1):
        modulus = (1 << cost) - 1
        g = gcd(cost, modulus)
        first_k = (g + 1) // 2
        for k in range(first_k, g + 1):
            slope = modulus * k // g
            if slope < 1 << (cost - 1) or slope == modulus:
                continue
            word = analyze_word(depths_from_bitmask(cost, slope))
            assert word.total_cost == cost
            assert word.slope == slope
            if word.certificate == "inconclusive":
                unresolved.append(word)
    return unresolved


def self_test() -> None:
    """Independent small identities and a finite 2048-cost search."""
    expected = {
        (0,): (2, 1, 1, -1, "inconclusive"),
        (1,): (4, 2, 2, 0, "primary"),
        (0, 1): (8, 5, 3, 3, "primary"),
        (1, 0): (8, 6, 3, 4, "primary"),
        (1, 1, 1): (64, 42, 6, 144, "secondary"),
    }
    for depths, values in expected.items():
        item = analyze_word(depths)
        assert (
            item.scale, item.slope, item.total_cost,
            item.constant, item.certificate,
        ) == values
    assert nontrivial_unresolved_words(2048) == []
