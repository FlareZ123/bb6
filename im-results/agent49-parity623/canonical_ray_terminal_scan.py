#!/usr/bin/env python3
"""Finite exact-integer audit of the canonical #623 ray terminal windows.

This is a reproducibility check, not an all-time nonhalting proof.  It imports
high_level_next from root_inverse_explorer.py, which mirrors the pinned
high-level source transition.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from typing import Any

from root_inverse_explorer import high_level_next


_LOG2_3_NUM = 1_584_962_500_721_156
_LOG2_3_DEN = 10**15


def min_exp_3_ge(target: int) -> int:
    """Least n with 3**n >= target, using an integer estimate and exact repair."""
    if target <= 1:
        return 0
    n = max(0, ((target.bit_length() - 1) * _LOG2_3_DEN) // _LOG2_3_NUM)
    while pow(3, n) < target:
        n += 1
    while n > 0 and pow(3, n - 1) >= target:
        n -= 1
    return n


def min_pow3_greater(value: int) -> int:
    return min_exp_3_ge(value + 1)


def min_tau_ge(value: int) -> int:
    """Least k with (3**k - 1)//2 >= value."""
    return min_exp_3_ge(2 * value + 1)


def min_right_odd_exponent(a: int) -> int:
    """Least k with a-1 <= tau(2*k+5)."""
    target = max(1, 2 * a - 1)
    exponent = min_exp_3_ge(target)
    k = max(0, (exponent - 5 + 1) // 2)
    while pow(3, 2 * k + 5) < target:
        k += 1
    while k > 0 and pow(3, 2 * (k - 1) + 5) >= target:
        k -= 1
    return k


def min_right_even_exponent(a: int) -> int:
    """Least k with a < tau(2*k+3)."""
    target = 2 * a + 3
    exponent = min_exp_3_ge(target)
    k = max(0, (exponent - 3 + 1) // 2)
    while pow(3, 2 * k + 3) < target:
        k += 1
    while k > 0 and pow(3, 2 * (k - 1) + 3) >= target:
        k -= 1
    return k


def canonical_ray(a: int, d: int) -> tuple[str, int, int, int, int, int] | None:
    """Return (sector, k, t, base_a, base_d, output_shift_factor)."""
    if d % 2 == 1 and a >= d + 5:
        k = min_tau_ge(d + 3)
        exponent = a - d - 5
        if exponent >= k:
            return "LO", k, exponent - k, d + 5 + k, d, 1

    if d % 2 == 0 and a >= d + 3:
        k = min_tau_ge(d + 2)
        exponent = a - d - 2
        if exponent >= k:
            return "LE", k, exponent - k, d + 2 + k, d, 1

    if a > 0 and a % 2 == 0 and a <= d and d % 2 == 1:
        k = min_right_odd_exponent(a)
        m = (d - a - 1) // 2
        if m >= k:
            return "RO", k, m - k, a, a + 1 + 2 * k, 2

    if a > 0 and a % 2 == 0 and a <= d and d % 2 == 0:
        k = min_right_even_exponent(a)
        m = d // 2 - a // 2 - 1
        if m >= k:
            return "RE", k, m - k, a, a + 2 + 2 * k, 2

    return None


def terminal_window(a: int, d: int, ray: tuple[str, int, int, int, int, int]) -> dict[str, int]:
    """Return exact distance from the canonical shift target and its ratio-4 width."""
    sector, k, t, _, _, _ = ray

    if sector == "LO":
        n = min_pow3_greater(d + 3)
        mass = a + 2 * d + 10 + 3 * n
        K = min_pow3_greater(2 * mass + 5)
        gap = abs(t - (3 * d - 5 - k))
        width = K + 5 * n + 29
    elif sector == "LE":
        n = min_pow3_greater(d + 2)
        mass = a + 2 * d + 7 + 3 * n
        K = min_pow3_greater(2 * mass + 5)
        gap = abs(t - (3 * d - 2 - k))
        width = K + 5 * n + 20
    elif sector == "RO":
        n = min_pow3_greater(a - 1)
        mass = d + 2 * a + 5 + 3 * n
        K = min_pow3_greater(2 * mass + 5)
        gap = abs(2 * t - (3 * a - 1 - 2 * k))
        width = K + 5 * n + 12
    else:
        n = min_pow3_greater(a)
        mass = d + 2 * a + 5 + 3 * n
        K = min_pow3_greater(2 * mass + 5)
        gap = abs(2 * t - (3 * a - 2 - 2 * k))
        width = K + 8 * n + 17

    return {"n": n, "mass": mass, "K": K, "gap": gap, "width": width, "margin": gap - width}


def run_scan(steps: int) -> dict[str, Any]:
    state = (0, 7)
    outside: list[dict[str, Any]] = []
    candidates: list[dict[str, Any]] = []
    mismatches: list[dict[str, Any]] = []
    sector_counts: Counter[str] = Counter()
    closest_excluded: dict[str, Any] | None = None
    canonical_count = 0
    halted_at: int | None = None
    checked = 0

    for index in range(steps):
        a, d = state
        ray = canonical_ray(a, d)

        if ray is None:
            outside.append({"index": index, "state": [a, d]})

        if index >= 9:
            if ray is None:
                mismatches.append({"index": index, "kind": "missing canonical ray", "state": [a, d]})
            else:
                canonical_count += 1
                sector, k, t, base_a, base_d, factor = ray
                sector_counts[sector] += 1

                base_output = high_level_next(base_a, base_d)
                actual_output = high_level_next(a, d)
                predicted_output = (
                    None if base_output is None else (base_output[0] + factor * t, base_output[1])
                )
                if predicted_output != actual_output:
                    mismatches.append(
                        {
                            "index": index,
                            "state": [a, d],
                            "ray": [sector, k, t, base_a, base_d, factor],
                            "base_output": base_output,
                            "actual_output": actual_output,
                            "predicted_output": predicted_output,
                        }
                    )

                window = terminal_window(a, d, ray)
                record = {
                    "index": index,
                    "state": [a, d],
                    "sector": sector,
                    "k": k,
                    "t": t,
                    **window,
                }
                if window["margin"] <= 0:
                    candidates.append(record)
                elif closest_excluded is None or window["margin"] < closest_excluded["margin"]:
                    closest_excluded = record

        next_state = high_level_next(a, d)
        checked = index + 1
        if next_state is None:
            halted_at = index
            break
        state = next_state

    return {
        "states_checked": checked,
        "halted_at": halted_at,
        "outside_new_affine_cone": outside,
        "canonical_states_from_index_9": canonical_count,
        "sector_counts": dict(sector_counts),
        "translation_mismatches": mismatches,
        "ratio4_window_candidates": candidates,
        "closest_excluded_candidate": closest_excluded,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", type=int, default=10_000)
    args = parser.parse_args()
    result = run_scan(args.steps)
    print(json.dumps(result, indent=2))
    if result["halted_at"] is not None or result["translation_mismatches"]:
        raise SystemExit(1)
    if args.steps == 10_000:
        assert result["states_checked"] == 10_000
        assert result["canonical_states_from_index_9"] == 9_991
        assert result["ratio4_window_candidates"][0]["index"] == 13
        assert result["closest_excluded_candidate"]["index"] == 16
        assert result["closest_excluded_candidate"]["margin"] == 2


if __name__ == "__main__":
    main()
