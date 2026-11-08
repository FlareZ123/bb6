#!/usr/bin/env python3
"""Exact arithmetic audit of high-valuation parents of the r=6
Space Needle cancellation feeder. Requires only Python standard library.
Combine with r6_low_polynomial.cpp for the exhaustive inverse exclusion.
"""
import math
import time

R = 6
PRIME_LIMIT = 10_000


def primes_up_to(n):
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(n) + 1):
        if sieve[p]:
            sieve[p*p:n+1:p] = b"\x00" * ((n-p*p)//p + 1)
    return [p for p in range(2, n+1) if sieve[p]]


def main():
    start = time.monotonic()
    nine = 9**R
    v = (nine + 3)//2
    K = R*(nine + 5)-1
    B0 = 1 << (v+1)
    q, rem = divmod((1 << K)-3*(1 << v)-v-3, B0+3)
    assert rem == 0 and q >= 0
    x = (1 << v)*(2*q+3)
    assert x.bit_length() == K
    N0 = 2*x+3
    assert 3**(2*R+1) < (1 << (v+2))

    rejected = bytearray(K+1)
    useful = 0
    for p in primes_up_to(PRIME_LIMIT):
        if p <= 3:
            continue
        z, exponent = 1, None
        for j in range(1, p):
            z = (2*z) % p
            if z == (p-3) and exponent is None:
                exponent = j
            if z == 1:
                if exponent is not None:
                    useful += 1
                    u0 = (exponent-1) % j
                    xmod = x % p
                    for u in range(u0, K+1, j):
                        if (2*xmod+3-2*u) % p:
                            rejected[u] = 1
                break

    removed = sum(rejected)
    low = sum(1 for u in range(v+1) if not rejected[u])
    high = K+1-removed-low
    print("r", R, "K", K, "v", v, "prime_witnesses", useful,
          "modularly_rejected", removed, "low_survivors", low,
          "high_survivors", high, flush=True)

    checked = 0
    hits = []
    for u in range(v+1, K+1):
        if rejected[u]:
            continue
        shift = u+1
        base = 1 << shift
        mask = base-1
        n = N0-2*u
        S, coeff, digits = 0, 1, 0
        while n:
            S += coeff*(n & mask)
            coeff *= -3
            n >>= shift
            digits += 1
        assert digits <= 2*R
        absS = abs(S)
        # Exact: |S| < base*3^(2R), and 3^(2R+1) < base,
        # so divisibility by base+3 implies quotient floor(|S|/base).
        if absS == (absS >> shift)*(base+3):
            hits.append(u)
        checked += 1
        if checked % 50000 == 0:
            print("high_checked", checked, "last_u", u,
                  "hits", len(hits), "elapsed", round(time.monotonic()-start, 2),
                  flush=True)
    assert checked == high
    print("FINISH", "high_checked", checked, "high_hits", hits,
          "seconds", round(time.monotonic()-start, 2), flush=True)
    assert not hits


if __name__ == "__main__":
    main()
