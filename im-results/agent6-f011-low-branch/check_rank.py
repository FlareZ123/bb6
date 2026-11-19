#!/usr/bin/env python3
"""Bounded diagnostic for the F011 high-level potential/rank candidate.

This checks the literal transition transcription over p in {False, True} and
0 <= k,c < bound. It is a regression diagnostic, not a proof of the universal
Lean theorems.
"""
from __future__ import annotations

import argparse
import json


def step(p: bool, k: int, c: int):
    q, r = divmod(k, 3)
    d = c - q

    if c < q:
        return (p, k - 3 * c - 2, 4 * c + 5)

    if p:
        if r == 0:
            if q == 0:
                return (False, 2, c + 2)
            if d == 0:
                return (False, 4 * q + 5, 1)
            if d == 1:
                return (False, 4 * q + 7, 1)
            if d == 2:
                return (True, 4 * q + 8, 1)
            return (True, 4 * q + 7, d - 2)
        if r == 1:
            if d == 0:
                return (False, 8, 4 * q + 1)
            if d == 1:
                return (False, 4 * q + 7, 1)
            return (False, 4 * q + 6, d - 1)
        if d == 0:
            return (True, 0, 4 * q + 5)
        if d == 1:
            return (False, 0, 4 * q + 9)
        if d == 2:
            return None
        if d == 3:
            return (False, 4 * q + 10, 0)
        if d == 4:
            return (False, 4 * q + 10, 3)
        return (False, 4 * q + 12, d - 5)

    if r == 0:
        if q == 0:
            if c == 0:
                return (False, 2, 3)
            return (False, 4, c - 1)
        if d == 0:
            return (True, 4 * q, 1)
        return (True, 4 * q - 1, d)
    if r == 1:
        if d == 0:
            return (False, 0, 4 * q + 3)
        if d == 1:
            return (False, 4 * q + 4, 1)
        return (False, 4 * q + 3, d - 1)
    if d == 0:
        return (False, 0, 4 * q + 5)
    if d == 1:
        return None
    if d == 2:
        return (False, 4 * q + 6, 0)
    if d == 3:
        return (False, 4 * q + 6, 3)
    return (False, 4 * q + 8, d - 4)


def potential(state) -> int:
    p, k, c = state
    q = k // 3
    phase_weight = 0 if not p else (2 if k == 0 else 3)
    return 3 * q + c + phase_weight


def rank(state):
    _, k, _ = state
    return (potential(state), int(k % 3 == 2))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bound", type=int, default=500,
                        help="check both k and c in range(bound)")
    args = parser.parse_args()
    bound = args.bound
    counts = {
        "states": 0,
        "defined_first_steps": 0,
        "terminal_states": 0,
        "zero_potential_steps": 0,
        "two_step_defined": 0,
        "minimum_two_step_increment": None,
    }

    for p in (False, True):
        for k in range(bound):
            for c in range(bound):
                s = (p, k, c)
                counts["states"] += 1
                t = step(*s)
                if t is None:
                    counts["terminal_states"] += 1
                    continue
                counts["defined_first_steps"] += 1
                if not rank(s) < rank(t):
                    raise AssertionError(("rank failure", s, t))
                if potential(s) == potential(t):
                    counts["zero_potential_steps"] += 1
                    if t[1] % 3 != 2:
                        raise AssertionError(("tie-break failure", s, t))

                u = step(*t)
                if u is not None:
                    counts["two_step_defined"] += 1
                    delta = potential(u) - potential(s)
                    if delta < 1:
                        raise AssertionError(("two-step growth failure", s, t, u, delta))
                    old = counts["minimum_two_step_increment"]
                    counts["minimum_two_step_increment"] = (
                        delta if old is None else min(old, delta)
                    )

    print(json.dumps(counts, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
