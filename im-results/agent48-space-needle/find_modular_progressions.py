#!/usr/bin/env python3
"""Enumerate prime-modulus Space Needle feeder-obstruction progressions.

For an odd prime p, let ord = ord_p(2). If 2^r = -3 (mod p), then p
divides 2^(v+1)+3 whenever v = r-1 (mod ord). For a fixed residue
b = v (mod p), a terminal feeder would also require 2^n = 2b-3 (mod p)
for some n. If 2b-3 is outside <2> in (Z/pZ)^*, that residue class is
impossible. CRT combines the two conditions into v = v0 (mod p*ord).

This is a discovery enumerator. The generic proof obligations are
formalized in SpaceNeedleObstructionFamilies.lean.
"""

from __future__ import annotations

import argparse
import csv
import math
import sys
from dataclasses import dataclass


@dataclass(frozen=True)
class Progression:
    v0: int
    period: int
    prime: int
    order: int
    log_minus_three: int
    v_mod_prime: int
    target_mod_prime: int


def primes_up_to(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            start = p * p
            sieve[start : limit + 1 : p] = b"\x00" * (((limit - start) // p) + 1)
    return [p for p, is_prime in enumerate(sieve) if is_prime]


def order_and_powers(prime: int) -> tuple[int, list[int]]:
    powers: list[int] = []
    seen: set[int] = set()
    value = 1
    while value not in seen:
        seen.add(value)
        powers.append(value)
        value = (2 * value) % prime
    return len(powers), powers


def progressions_for_prime(prime: int) -> list[Progression]:
    if prime == 2:
        return []
    order, powers = order_and_powers(prime)
    powers_set = set(powers)
    try:
        log_minus_three = powers.index((-3) % prime)
    except ValueError:
        return []

    exponent_residue = (log_minus_three - 1) % order
    inverse_order = pow(order, -1, prime)
    period = prime * order
    result: list[Progression] = []

    for v_mod_prime in range(prime):
        target = (2 * v_mod_prime - 3) % prime
        if target in powers_set:
            continue
        crt_multiplier = ((v_mod_prime - exponent_residue) * inverse_order) % prime
        v0 = exponent_residue + order * crt_multiplier
        assert 0 <= v0 < period
        assert v0 % order == exponent_residue
        assert v0 % prime == v_mod_prime
        assert pow(2, v0 + 1, prime) == (-3) % prime
        assert pow(2, period, prime) == 1
        assert target not in powers_set
        result.append(
            Progression(
                v0=v0,
                period=period,
                prime=prime,
                order=order,
                log_minus_three=log_minus_three,
                v_mod_prime=v_mod_prime,
                target_mod_prime=target,
            )
        )
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prime-limit", type=int, default=103)
    parser.add_argument("--min-prime", type=int, default=5)
    args = parser.parse_args()

    rows = [
        progression
        for prime in primes_up_to(args.prime_limit)
        if prime >= args.min_prime
        for progression in progressions_for_prime(prime)
    ]
    rows.sort(key=lambda row: (row.v0, row.period, row.prime, row.v_mod_prime))

    writer = csv.writer(sys.stdout, lineterminator="\n")
    writer.writerow(
        [
            "v0",
            "period",
            "prime",
            "ord2",
            "log2_minus3",
            "v_mod_prime",
            "target_mod_prime",
        ]
    )
    for row in rows:
        writer.writerow(
            [
                row.v0,
                row.period,
                row.prime,
                row.order,
                row.log_minus_three,
                row.v_mod_prime,
                row.target_mod_prime,
            ]
        )


if __name__ == "__main__":
    main()
