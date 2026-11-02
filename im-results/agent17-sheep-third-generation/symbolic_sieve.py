#!/usr/bin/env python3
"""Parametric symbolic backward sieve for the published Sheep return map.

For every residue r modulo MODULUS, certify that no defined iterate of F(5)
equals 2**j when j >= MIN_EXPONENT and j % MODULUS == r, provided the bounded
inverse tree closes. The finitely many smaller exponents are checked using
strict monotonicity of F. The arithmetic claims behind the certificates are
derived in SYMBOLIC-SIEVE.md.

The SymPy n_order routine proposes periods; every proposed period is verified
by built-in modular exponentiation before it is trusted. No floating point,
random choices, heuristics or arbitrary forward-step cutoffs enter the proof.
"""
from dataclasses import dataclass
from functools import lru_cache
from hashlib import sha256
from math import gcd

from sympy.ntheory import n_order

MODULUS = 5400
MIN_EXPONENT = 100
DEPTH = 3
EXPECTED_EXCLUDED = 3544
EXPECTED_SHA256 = "3501152b8f0e5feb4d45fce3505e4457264d2f6001b2ea675508abde300ccb37"


@dataclass(frozen=True)
class Family:
    """Represents the rational expression (2**(j + shift) + b) / d."""

    shift: int
    b: int
    d: int

    def predecessor(self, a: int) -> "Family":
        power = 1 << a
        return Family(
            self.shift + a + 1,
            (2 * power) * self.b + power * self.d * (1 - 2 * a),
            self.d * (2 * power + 1),
        )


def next_section(t: int) -> int | None:
    """The published one-counter map F; inputs here are positive."""
    assert t >= 1
    a = (t & -t).bit_length() - 1
    u = t >> a
    if u == 1:
        return None
    if u == 3:
        return t + a + 3
    return t + a + (u - 1) // 2


def generic_tail_bound(f: Family) -> int:
    """All generic predecessors with a >= returned bound are impossible.

    K(a) = d*(2*a-1)-2*b is odd. Once 1<K(a)<2**a and 2**a>=2*d,
    those inequalities persist by induction and the Fermat-modulus lemma
    excludes the required power-of-two congruence.
    """
    a = 0
    while True:
        power = 1 << a
        k = f.d * (2 * a - 1) - 2 * f.b
        if 1 < k < power and power >= 2 * f.d:
            return a
        a += 1


def exceptional_threshold(f: Family) -> int:
    """For every j >= threshold, no u=3 predecessor is possible.

    Choose s with 2**(shift+s) < 3*d < 2**(shift+s+1).
    A candidate t=3*2**a has a >= j-s or a <= j-s-1. Exact
    integer inequalities separate both possibilities at j=J and preserve
    strictness inductively for every larger j.
    """
    s = (3 * f.d).bit_length() - 1 - f.shift
    assert s >= 0
    high_gap = 3 * f.d - (1 << (f.shift + s))
    low_gap = (1 << (f.shift + s + 1)) - 3 * f.d
    assert high_gap > 0 and low_gap > 0
    j = max(5, s + 1)
    while True:
        q = 1 << j
        high_ok = high_gap * q > f.b * (1 << s)
        low_ok = low_gap * q > (1 << (s + 1)) * (f.d * (j + 3) - f.b)
        growth_ok = low_gap * q > (1 << (s + 1)) * f.d
        if high_ok and low_ok and growth_ok:
            return j
        j += 1


@lru_cache(maxsize=None)
def checked_period(modulus: int) -> int:
    """A certified usable period, even if the external order code errs."""
    period = int(n_order(2, modulus))
    assert period > 0 and pow(2, period, modulus) == 1
    return period


@lru_cache(maxsize=None)
def candidate_valuations(f: Family, residue: int, modulus: int) -> tuple[int, ...]:
    """A sound overapproximation of all generic inverse valuations.

    Computes exact necessary congruences for ALL exponents j in the class.
    A candidate may fail to yield an odd, sufficiently large, integral u;
    such false positives weaken the certificate but never invalidate it.
    """
    assert exceptional_threshold(f) <= MIN_EXPONENT, (f, "exceptional branch")
    assert (1 << (MIN_EXPONENT + f.shift)) + f.b > 5 * f.d, (f, "equals initial 5")

    found = []
    for a in range(generic_tail_bound(f)):
        m = f.d * ((1 << (a + 1)) + 1)
        target = (f.d * (2 * a - 1) - 2 * f.b) % m
        period = checked_period(m)
        checks = period // gcd(period, modulus)
        # Verify the optimized class period independently. PeriodCore.lean
        # proves that this single assertion covers every exponent in class.
        assert checks > 0 and pow(2, modulus * checks, m) == 1
        if any(
            pow(2, residue + f.shift + 1 + modulus * k, m) == target
            for k in range(checks)
        ):
            found.append(a)
    return tuple(found)


def inverse_tree_closes(f: Family, residue: int, modulus: int, remaining_depth: int) -> bool:
    valuations = candidate_valuations(f, residue, modulus)
    if not valuations:
        return True
    if remaining_depth == 0:
        return False
    return all(
        inverse_tree_closes(f.predecessor(a), residue, modulus, remaining_depth - 1)
        for a in valuations
    )


def check_small_exponents() -> int:
    """Exhaust all targets below 2**MIN_EXPONENT in one exact forward trace."""
    highest = 1 << (MIN_EXPONENT - 1)
    t = 5
    steps = 0
    while t <= highest:
        assert t & (t - 1), ("unexpected reached halting power", steps, t)
        successor = next_section(t)
        assert successor is not None and successor > t
        t = successor
        steps += 1
    return steps


def verify() -> None:
    finite_steps = check_small_exponents()
    root = Family(0, 0, 1)
    excluded = [
        r for r in range(MODULUS)
        if inverse_tree_closes(root, r, MODULUS, DEPTH)
    ]
    result = sha256(",".join(map(str, excluded)).encode("ascii")).hexdigest()
    assert len(excluded) == EXPECTED_EXCLUDED, len(excluded)
    assert result == EXPECTED_SHA256, result

    print(f"Finite prefix: {finite_steps} strictly increasing section steps")
    print(f"Uniform theorem: all j >= {MIN_EXPONENT} with j mod {MODULUS} in")
    print(f"{len(excluded)} certified classes are unreachable from t=5")
    print(f"Certificate class-list SHA256: {result}")
    print(f"Unique modular periods verified: {checked_period.cache_info().currsize}")
    print("PASS: symbolic inverse-tree modular certificate")


if __name__ == "__main__":
    verify()
