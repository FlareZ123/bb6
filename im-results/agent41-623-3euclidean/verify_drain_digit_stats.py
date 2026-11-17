#!/usr/bin/env python3
"""Reproduce the 3-adic / ternary-digit drain identities for source #623.

No external dependencies.  The evaluator and drain below mirror the definitions
in the pinned BusyBeaver source; the closed form is computed independently from
ordinary base-three digits.
"""

from __future__ import annotations


def tau(n: int) -> int:
    return (3**n - 1) // 2


def eval_a(a: int, k: int, m: int):
    """Exact source evalA recursion, written iteratively."""
    while True:
        if k % 3 == 2:
            return (a + 1, k // 3, m)
        if a == 0:
            if k % 3 == 0:
                return None
            return (0, k // 3, m)
        if k % 3 == 0:
            return (a - 1, k // 3, m + 2)
        a -= 1
        k //= 3
        m += 2 * k + 3


def drain_b(a: int, b: int, d: int):
    """Exact source drainB recursion; returns (first, third, iterations)."""
    iterations = 0
    while b:
        old_b = b
        out = eval_a(a, b - 1, d + 2 * b + 3)
        if out is None:
            return None
        a, b, d = out
        if b >= old_b:
            return None
        iterations += 1
    return (a, d, iterations)


def valuation_signature(b: int):
    """Return (L,e,Delta,r) by the recursive 3-adic valuation descent."""
    if b <= 0:
        return (0, 0, 0, 0)
    L = e = Delta = r = 0
    while b:
        x = 2 * b - 1
        v = 0
        while x % 3 == 0:
            x //= 3
            v += 1
        eps = 1 if x % 6 == 5 else 0
        b_next = (x - 1 - 4 * eps) // 6
        assert 0 <= b_next < b
        L += v + 1
        e += eps
        Delta += 1 - 2 * eps
        r += 1
        b = b_next
    return (L, e, Delta, r)


def ternary_depth(b: int) -> int:
    """Unique L == b (mod 2) with 3^(L-1) <= 2b-1 < 3^(L+1)."""
    assert b > 0
    x = 2 * b - 1
    n, power = 0, 1
    while power * 3 <= x:
        power *= 3
        n += 1
    return n if n % 2 == b % 2 else n + 1


def closed_signature(b: int):
    """Return (L,e,Delta,r) from the single integer N=(2b-1+3^L)/4."""
    if b <= 0:
        return (0, 0, 0, 0)
    L = ternary_depth(b)
    numerator = 2 * b - 1 + 3**L
    assert numerator % 4 == 0
    N = numerator // 4
    e = Delta = r = 0
    while N:
        digit = N % 3
        if digit:
            r += 1
        if digit == 1:
            Delta += 1
        elif digit == 2:
            e += 1
            Delta -= 1
        N //= 3
    return (L, e, Delta, r)


def closed_drain(a: int, b: int, d: int):
    """Nonrecursive drain formula from the ternary digit statistics."""
    L, e, Delta, _r = closed_signature(b)
    return (a - L + 2 * e, d + 3 * b + 2 * L + 2 * Delta)


def check_digit_statistics(limit: int = 100_000) -> int:
    for b in range(1, limit + 1):
        recursive = valuation_signature(b)
        direct = closed_signature(b)
        assert recursive == direct, (b, recursive, direct)
    return limit


def check_evaluator_formula(limit: int = 10_000) -> int:
    checked = 0
    for b in range(1, limit + 1):
        x = 2 * b - 1
        v = 0
        while x % 3 == 0:
            x //= 3
            v += 1
        eps = 1 if x % 6 == 5 else 0
        b_next = (x - 1 - 4 * eps) // 6
        expected_tail = (6 * b_next + 1 + 4 * eps) * tau(v) + 2 * v + 2 * (1 - eps)
        for a in range(v + 1, v + 5):
            m = 17
            actual = eval_a(a, b - 1, m)
            expected = (a - v - 1 + 2 * eps, b_next, m + expected_tail)
            assert actual == expected, (b, a, actual, expected)
            checked += 1
    return checked


def check_whole_drain(limit_a: int = 80, cap_b: int = 200) -> int:
    checked = 0
    for a in range(2, limit_a + 1):
        for b in range(1, min(tau(a), cap_b) + 1):
            actual = drain_b(a, b, 5)
            expected = (*closed_drain(a, b, 5), valuation_signature(b)[3])
            assert actual == expected, (a, b, actual, expected)
            checked += 1
    return checked


def check_canonical_exponent(limit: int = 100_000) -> int:
    for b in range(1, limit + 1):
        L, e, Delta, _r = closed_signature(b)
        N = (2 * b - 1 + 3**L) // 4
        sigma = 1 if N > tau(L) else 0
        A = 0
        while b > tau(A):
            A += 1
        assert A == L + sigma, (b, L, N, sigma, A)
    return limit


if __name__ == "__main__":
    n_digits = check_digit_statistics()
    n_eval = check_evaluator_formula()
    n_drain = check_whole_drain()
    n_exponent = check_canonical_exponent()
    print(f"closed digit signatures: {n_digits:,} counters passed")
    print(f"one-step evaluator formula: {n_eval:,} calls passed")
    print(f"whole drain normal form: {n_drain:,} budgeted inputs passed")
    print(f"canonical exponent formula: {n_exponent:,} counters passed")
