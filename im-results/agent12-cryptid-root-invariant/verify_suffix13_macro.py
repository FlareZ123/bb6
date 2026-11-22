#!/usr/bin/env python3
"""Finite source-transcribed checks for the #85 offset-six macros.

This is not a machine simulator or a proof. It transcribes only the ordinary
CR/EL/DL/DR stack clauses used by the suffix-[13] decrement and E_n(1) bridge.
All stacks are first-coordinate lists; bumpPairHead([]) is [0].
"""
from __future__ import annotations

def bump(xs):
    return [0] if not xs else [xs[0] + 1] + xs[1:]

def bumpn(xs, k):
    for _ in range(k):
        xs = bump(xs)
    return xs

def step(mode, left, right):
    if mode == "CR":
        if not left:
            return ("EL", [0], bump(right), 2)
        a, *l3 = left
        if a == 0:
            return ("CR", l3, bumpn(right, 2), 2)
        if a == 1:
            if not l3:
                return ("EL", [0], [0] + bumpn(right, 3), 6)
            b, *l8 = l3
            if b == 0:
                return ("CR", l8, [0] + bumpn(right, 3), 5)
            if b == 1:
                return ("EL", bump(l8), [1, 0, 0] + right, 16)
            return ("DR", [b - 2] + l8, [1, 0, 0] + right, 15)
        return ("HALT", [], [], 2)

    if mode == "EL":
        if not right:
            return ("CR", left, [0], 1)
        r, *r3 = right
        if r == 0:
            return ("EL", [0] + left, r3, 2)
        return ("DL", left, [r - 1] + r3, 1)

    if mode == "DL":
        if not right:
            return ("CR", left, [2], 4)
        r, *r3 = right
        if r == 0:
            return ("EL", [0] + bump(left), r3, 6)
        if r == 1:
            return ("TOKEN", left, r3, 4)
        return ("DR", left, [1, r - 2] + r3, 4)

    if mode == "DR":
        if not left:
            return ("EL", [0], right, 1)
        a, *l3 = left
        if not right:
            if a == 0:
                return ("EL", bump(l3), [0], 4)
            return ("DR", [a - 1] + l3, [0], 3)
        r, *r3 = right
        if r == 0:
            if a == 0:
                return ("TOKEN_DR", l3, r3, 4)
            return ("TOKEN_CR", [a] + l3, r3, 3)
        if a == 0:
            return ("DR", l3, [1, r - 1] + r3, 4)
        return ("CR", [a - 1] + l3, [0, r - 1] + r3, 3)

    raise ValueError(mode)

def run_steps(mode, left, right, count):
    raw = 0
    for i in range(count):
        mode, left, right, cost = step(mode, left, right)
        raw += cost
        if mode.startswith("TOKEN") or mode == "HALT":
            raise AssertionError(f"unexpected {mode} at successor {i + 1}")
    return mode, left, right, count, raw

def E(n, x, suffix=()):
    return ("CR", [0], [0] * (4 * n + 6) + [x] + list(suffix))

# E_n(x;T) -> E_(n+1)(x-3;T), x >= 3.
for n in range(5):
    for x in (3, 4, 7, 10, 13, 16):
        count = 8 * n + 26
        got = run_steps(*E(n, x, (13, 0)), count)
        expected = E(n + 1, x - 3, (13, 0))
        assert got[:3] == expected, (n, x, got[:3], expected)
        assert got[3:] == (count, 24 * n + 75), (n, x, got[3:])

# Four decrements: E_n(13) -> E_(n+4)(1).
for n in range(5):
    mode, left, right = E(n, 13)
    outer = raw = 0
    for j in range(4):
        count = 8 * (n + j) + 26
        mode, left, right, steps, cost = run_steps(mode, left, right, count)
        outer += steps
        raw += cost
    expected = E(n + 4, 1)
    assert (mode, left, right) == expected
    assert outer == 32 * n + 152
    assert raw == 96 * n + 444

# E_n(1) -> D_0(8n+9;[5]).
for n in range(5):
    count = 8 * n + 43
    got = run_steps(*E(n, 1), count)
    expected = ("CR", [0], [0] * 5 + [8 * n + 9, 5])
    assert got[:3] == expected, (n, got[:3], expected)
    assert got[3:] == (count, 16 * n + 115), (n, got[3:])

print("PASS: 30 decrement cases, 5 four-step suffix-[13] chains, 5 E_n(1) bridges")
