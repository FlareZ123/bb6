#!/usr/bin/env python3
"""Arithmetic sanity checks for S2OddBouncePullback.md.

This checks 100 representatives of the congruence cylinder. It does NOT
verify the source-preimage classification or prove blank-root nonreachability.
"""
from __future__ import annotations


MOD_V = 128
MOD_M = 131072

for u in range(100):
    # Least nonnegative v with v + 93*u == 42 (mod 128).
    v = (42 - 93 * u) % MOD_V
    assert (v + 93 * u) % MOD_V == 42

    s = u + v
    assert s >= 2 and s % 4 == 2
    t = (s - 2) // 4
    assert (v - (28 + 11 * t)) % 32 == 0

    rx = 471 + 276 * u + 548 * v
    ry = 644 + 374 * u + 750 * v
    px = 1113 + 650 * u + 1298 * v
    py = 321 + 187 * u + 375 * v
    qx = 601 + 650 * t + 162 * v
    qy = 1598 + 1723 * t + 431 * v

    T = 558 + 325 * u + 649 * v
    assert (rx + ry + 1) == 2 * T
    assert T % 16 == 8

    assert px % 2 == 1 and py % 2 == 1
    psum = px + py
    assert psum % 4 == 0 and psum % 16 in (4, 12)

    A = 1552 + 1674 * t + 418 * v
    B = 1122 + 1211 * t + 303 * v
    assert A % 16 == 8
    assert B % 32 == 6
    assert (B + 2) % 8 == 0
    W = (B + 2) // 8
    assert W >= 141 and W % 4 == 1

    F1 = (A + 8 * W - 4, 4 * W - 2)
    F2 = (A + 12 * W - 8, 2 * W - 2)
    F3 = (A + 14 * W - 12, W - 2)
    assert (A + B) % 8 == 6
    assert sum(F1) % 8 == 6
    assert sum(F2) % 8 == 4
    assert B % 2 == 0 and F1[1] % 2 == 0 and F2[1] % 2 == 0
    assert F3[1] % 2 == 1 and sum(F3) % 4 == 1

    assert (qx + qy) % 8 == 3
    assert qy % 16 == 2 and qy >= 34

    j = 319 + 512 * u
    m = (72746 + 75264 * u) % MOD_M
    assert m % 512 == 42
    assert (3 * m + 102921 - 185 * j) % MOD_M == 0
    assert (574 + 1024 * v) % MOD_M == (43582 - 95232 * u) % MOD_M

print("S2 arithmetic sanity checks passed for u=0,...,99.")
