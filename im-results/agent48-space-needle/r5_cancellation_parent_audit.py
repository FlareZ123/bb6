#!/usr/bin/env python3
"""Exact inverse-parent audit for the r=5 Space Needle cancellation feeder.

This is a reproducible finite arithmetic computation. It does not rely on
floating point, external packages, or a simulator. It checks every possible
2-adic valuation of an incoming parent using (i) exact division for u<=v,
(ii) small-prime modular rejection, then (iii) an exact signed base-2^(u+1)
remainder identity for the remaining u>v.
"""
from __future__ import annotations

import hashlib
import json
import math
import random
import time

R = 5
PRIME_LIMIT = 10_000


def primes_up_to(n: int) -> list[int]:
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(n) + 1):
        if sieve[p]:
            start = p * p
            sieve[start : n + 1 : p] = b"\x00" * (((n - start) // p) + 1)
    return [p for p in range(2, n + 1) if sieve[p]]


def cancellation_feeder(r: int) -> tuple[int, int, int, int]:
    """Return (K,v,q,x), where x=oddTower(q,v)+2."""
    nine_r = 9**r
    v = (nine_r + 3) // 2
    K = r * (nine_r + 5) - 1
    denominator = (1 << (v + 1)) + 3
    bias = 3 * (1 << v) + v + 3
    q, rem = divmod((1 << K) - bias, denominator)
    assert rem == 0 and q >= 0
    x = (1 << v) * (2 * q + 3)
    assert x.bit_length() == K
    assert x < (1 << K)
    return K, v, q, x


def prime_order_and_log(p: int) -> tuple[int, int] | None:
    """Find L=ord_p(2) and e with 2^e=-3 mod p, if one exists."""
    z = 1
    e = None
    for j in range(1, p):
        z = (2 * z) % p
        if z == (-3) % p and e is None:
            e = j
        if z == 1:
            if e is None:
                return None
            return j, e
    return None


def signed_base_remainder(n: int, u: int) -> tuple[int, int, int]:
    """Return S,L,B with S=sum_i digit_i*(-3)^i and B=2^(u+1).

    Writing n=sum_i digit_i*B^i gives S == n (mod B+3).
    """
    B = 1 << (u + 1)
    mask = B - 1
    t = n
    S = 0
    coefficient = 1
    digits = 0
    while t:
        S += coefficient * (t & mask)
        coefficient *= -3
        t >>= u + 1
        digits += 1
    return S, digits, B


def main() -> None:
    started = time.time()
    K, v, q, x = cancellation_feeder(R)
    N0 = 2 * x + 3
    ps = primes_up_to(PRIME_LIMIT)
    witness: dict[int, int] = {}
    useful_primes = 0

    # If p | (2^(u+1)+3), then 2^(u+1) == -3 (mod p),
    # so u == e-1 (mod ord_p(2)). Such a parent also requires
    # p | (2*x+3-2*u). Any failure rejects u exactly.
    for p in ps:
        if p <= 3:
            continue
        order_log = prime_order_and_log(p)
        if order_log is None:
            continue
        order, exponent = order_log
        assert pow(2, order, p) == 1
        assert pow(2, exponent, p) == p - 3
        useful_primes += 1
        u0 = (exponent - 1) % order
        x_mod_p = x % p
        for u in range(u0, K + 1, order):
            if u not in witness and (2 * x_mod_p + 3 - 2 * u) % p != 0:
                witness[u] = p

    # For u <= v, check the full exact divisibility directly.
    low_checked = 0
    low_divisible: list[tuple[int, int]] = []
    for u in range(v + 1):
        if u in witness:
            continue
        B = (1 << (u + 1)) + 3
        N = N0 - 2 * u
        a, rem = divmod(N, B)
        low_checked += 1
        if rem == 0:
            low_divisible.append((u, a))

    # For u > v, first reject all u witnessed by a small prime. For each
    # survivor, use B=2^(u+1), B == -3 (mod B+3), and the signed digit sum S.
    # Since N has at most 2R base-B digits and 3^(2R+1) < B, if B+3 | S,
    # then |S|//B is exactly the quotient |S|/(B+3). Thus divisibility is
    # decided by one exact multiplication, without a large integer division.
    high_checked = 0
    high_divisible: list[tuple[int, int]] = []
    max_digits = 0
    for u in range(v + 1, K + 1):
        if u in witness:
            continue
        N = N0 - 2 * u
        S, digits, B = signed_base_remainder(N, u)
        max_digits = max(max_digits, digits)
        assert digits <= 2 * R
        assert 3 ** (2 * R + 1) < B
        abs_S = abs(S)
        quotient = abs_S >> (u + 1)
        if abs_S == quotient * (B + 3):
            a, rem = divmod(N, B + 3)
            assert rem == 0
            high_divisible.append((u, a))
        high_checked += 1

    assert not low_divisible
    assert not high_divisible

    # Independent spot-check of the signed-remainder predicate against
    # direct exact division on a deterministic sample of high survivors.
    survivors_for_sample = [u for u in range(v + 1, K + 1) if u not in witness]
    sample = random.Random(20261107).sample(
        survivors_for_sample, min(256, len(survivors_for_sample))
    )
    for u in sample:
        N = N0 - 2 * u
        D = (1 << (u + 1)) + 3
        S, _, B = signed_base_remainder(N, u)
        fast = abs(S) == (abs(S) >> (u + 1)) * (B + 3)
        exact = N % D == 0
        assert fast == exact

    bad_low = sum(1 for u in witness if u <= v)
    bad_high = sum(1 for u in witness if v < u <= K)
    low_survivors = low_checked
    high_survivors = high_checked
    assert bad_low + low_survivors == v + 1
    assert bad_high + high_survivors == K - v

    bad_hash = hashlib.sha256(
        b"".join(u.to_bytes(4, "little") for u in sorted(witness))
    ).hexdigest()
    witness_hash = hashlib.sha256(
        b"".join(
            u.to_bytes(4, "little") + witness[u].to_bytes(4, "little")
            for u in sorted(witness)
        )
    ).hexdigest()
    survivors = [u for u in range(v + 1, K + 1) if u not in witness]
    survivor_hash = hashlib.sha256(
        b"".join(u.to_bytes(4, "little") for u in survivors)
    ).hexdigest()
    summary = {
        "r": R,
        "K": K,
        "v": v,
        "q_bits": q.bit_length(),
        "target_bits": x.bit_length(),
        "target_below_2_pow_K": x < (1 << K),
        "prime_limit": PRIME_LIMIT,
        "primes_tested": len(ps),
        "useful_primes": useful_primes,
        "modularly_rejected_u": len(witness),
        "modular_rejection_sha256": bad_hash,
        "modular_witness_sha256": witness_hash,
        "rejected_low": bad_low,
        "rejected_high": bad_high,
        "low_exact_checks": low_checked,
        "low_survivors": low_survivors,
        "high_signed_remainder_checks": high_checked,
        "high_survivors": len(survivors),
        "high_survivor_sha256": survivor_hash,
        "sampled_signed_remainder_cross_checks": len(sample),
        "maximum_signed_digit_count": max_digits,
        "low_divisible": low_divisible,
        "high_divisible": high_divisible,
        "total_valuation_range_checked": K + 1,
        "parents_found": 0,
        "elapsed_seconds": round(time.time() - started, 3),
    }
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
