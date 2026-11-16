#!/usr/bin/env python3
"""Exact forward reset-orbit, 3-adic coverage, and special L=K+1 adjacent-fatal audit.

This is an executable transcription of the ResetParent equations formalized in
im-results/agent10-cascade/FirstInverseComplete.lean. The added B0/B1 odd-part
tests cover only adjacent-even fatal histories; direct odd-output fatality is
a separate all-t branch. All output is finite computational evidence, not a
proof of nonhalting.
"""

from __future__ import annotations

import argparse
import json


def first_failed_k(h: int) -> int:
    """Least k with h + k + 5 < 8*2^k.

    If m=floor(log2(h)), no k <= m-3 can work because
    8*2^k <= 2^m <= h <= h+k+5.  Thus the search starts at max(0,m-2).
    """
    m = h.bit_length() - 1
    k = max(0, m - 2)
    while h + k + 5 >= (8 << k):
        k += 1
    return k


def reset_step(h: int) -> tuple[int, int, str, int] | None:
    """Return (child, source level k, branch, t), or None at a fatal height."""
    k = first_failed_k(h)
    p = 1 << k

    if h + k + 4 == 4 * p:
        return None

    s = h + k
    if s % 2 == 0:
        # 2u = 8*2^k + h + k
        return 4 * p + s // 2, k, "even", 0

    # 2x = 8*2^k + h + k + 5, x = 2^t*d, d odd.
    q = 4 * p + s // 2 + 3
    t = 0
    while q % 2 == 0:
        q //= 2
        t += 1
    # 2u + 5 = 3^(t+1)*d
    return (pow(3, t + 1) * q - 5) // 2, k, "odd", t



def two_adic_odd_part(value: int) -> tuple[int, int] | None:
    """Return (v2(value), odd_part(value)) for positive values."""
    if value <= 0:
        return None
    exponent = 0
    while value % 2 == 0:
        value //= 2
        exponent += 1
    return exponent, value

def run(steps: int) -> dict:
    h = 2
    current_k = first_failed_k(h)
    transitions = 0
    entries = 0
    events = 0
    exits = {"even": 0, "odd": 0}
    max_t = 0
    adjacent_fatal_oddpart = {
        "t0": {
            "odd_exits": 0, "positive": 0, "divisible_by_2K_plus_7": 0,
            "power_of_two_quotients": 0, "adjacent_even_matches": 0,
            "first_divisible": None, "first_match": None,
        },
        "t1": {
            "odd_exits": 0, "positive": 0, "divisible_by_2K_plus_7": 0,
            "power_of_two_quotients": 0, "direct_odd_output_matches": 0,
            "adjacent_even_matches": 0, "first_divisible": None,
            "first_match": None,
        },
        "odd_exits_t_ge_2": 0,
        "scope": (
            "Adjacent-even fatality only: t>=2 is excluded by the source-band "
            "inequality; t=0 and t=1 require the displayed odd-part tests. "
            "Direct odd-output fatality is a separate all-t case."
        ),
    }
    all_entries_mod3_eq_2 = True
    all_exits_from_k4_odd = True
    all_residuals_from_k4_large = True
    min_margin = None
    min_margin_k = None

    precisions = range(2, 9)
    moduli = {a: 3**a for a in precisions}
    seen = {a: set() for a in precisions}
    first_full = {a: None for a in precisions}
    fatal_matches = {a: 0 for a in precisions}

    def record_entry(k: int, height: int) -> None:
        nonlocal entries, all_entries_mod3_eq_2
        entries += 1
        if height % 3 != 2:
            all_entries_mod3_eq_2 = False
        for a in precisions:
            modulus = moduli[a]
            residue = height % modulus
            seen[a].add(residue)
            if first_full[a] is None and len(seen[a]) == 3 ** (a - 1):
                first_full[a] = entries
            fatal = 4 * (1 << k) - k - 4
            if residue == fatal % modulus:
                fatal_matches[a] += 1

    record_entry(current_k, h)
    halt_after = None

    for _ in range(steps):
        result = reset_step(h)
        if result is None:
            halt_after = transitions
            break

        child, k, branch, t = result
        next_k = first_failed_k(child)
        if next_k < k:
            raise AssertionError(f"level decreased: {k} -> {next_k}")
        if branch == "odd":
            max_t = max(max_t, t)
            if next_k == k:
                raise AssertionError("odd reset unexpectedly stayed at its source level")

            c = 2 * k + 7
            if t == 0:
                stats = adjacent_fatal_oddpart["t0"]
                stats["odd_exits"] += 1
                B0 = 40 * p + k - 1 - 3 * h
                if B0 > 0:
                    stats["positive"] += 1
                    if B0 % c == 0:
                        stats["divisible_by_2K_plus_7"] += 1
                        quotient = B0 // c
                        v = two_adic_odd_part(quotient)
                        if stats["first_divisible"] is None:
                            stats["first_divisible"] = {
                                "transition": transitions, "K": k, "height": h,
                                "B0": B0, "odd_factor": c, "quotient": quotient,
                                "v2": v[0], "odd_part": v[1],
                            }
                        if v[1] == 1:
                            stats["power_of_two_quotients"] += 1
                            if v[0] >= 4 and v[0] % 2 == 0:
                                stats["adjacent_even_matches"] += 1
                                if stats["first_match"] is None:
                                    stats["first_match"] = {
                                        "transition": transitions, "K": k,
                                        "height": h, "v2": v[0],
                                        "even_reset_count": v[0] - 3,
                                    }
            elif t == 1:
                stats = adjacent_fatal_oddpart["t1"]
                stats["odd_exits"] += 1
                B1 = 112 * p - 2 * k - 34 - 18 * h
                if B1 > 0:
                    stats["positive"] += 1
                    if B1 % 8 != 0:
                        raise AssertionError("t=1 B1 not divisible by 8")
                    if B1 % c == 0:
                        stats["divisible_by_2K_plus_7"] += 1
                        quotient = B1 // c
                        v = two_adic_odd_part(quotient)
                        if stats["first_divisible"] is None:
                            stats["first_divisible"] = {
                                "transition": transitions, "K": k, "height": h,
                                "B1": B1, "odd_factor": c, "quotient": quotient,
                                "v2": v[0], "odd_part": v[1],
                            }
                        if v[1] == 1:
                            stats["power_of_two_quotients"] += 1
                            if v[0] == 4:
                                stats["direct_odd_output_matches"] += 1
                            elif v[0] >= 6 and v[0] % 2 == 0:
                                stats["adjacent_even_matches"] += 1
                                if stats["first_match"] is None:
                                    stats["first_match"] = {
                                        "transition": transitions, "K": k,
                                        "height": h, "v2": v[0],
                                        "even_reset_count": v[0] - 5,
                                    }
            else:
                adjacent_fatal_oddpart["odd_exits_t_ge_2"] += 1

        if next_k > k:
            events += 1
            exits[branch] += 1
            if k >= 4:
                residual = 8 * (1 << k) + k - h
                margin = residual - (4 * k + 10)
                if residual % 2 == 0:
                    all_exits_from_k4_odd = False
                if margin <= 0:
                    all_residuals_from_k4_large = False
                if min_margin is None or margin < min_margin:
                    min_margin = margin
                    min_margin_k = k
            record_entry(next_k, child)

        h = child
        transitions += 1
        current_k = next_k

    coverage = []
    for a in precisions:
        coverage.append(
            {
                "power": a,
                "modulus": moduli[a],
                "possible_residues_congruent_2_mod_3": 3 ** (a - 1),
                "seen_residues": len(seen[a]),
                "first_full_prefix_length": first_full[a],
                "same_level_fatal_congruence_matches": fatal_matches[a],
                "missing_residues": sorted(
                    set(range(2, moduli[a], 3)) - seen[a]
                ),
            }
        )

    return {
        "requested_transitions": steps,
        "completed_transitions": transitions,
        "halt_after_transitions": halt_after,
        "level_entries_including_root": entries,
        "level_exit_events": events,
        "level_exit_branch_counts": exits,
        "max_odd_exponent_t": max_t,
        "final_level": first_failed_k(h),
        "final_log2_height": h.bit_length() - 1,
        "final_height_bits": h.bit_length(),
        "all_level_entries_congruent_2_mod_3": all_entries_mod3_eq_2,
        "all_level_exits_from_K_ge_4_odd": all_exits_from_k4_odd,
        "all_terminal_residuals_from_K_ge_4_gt_4K_plus_10":
            all_residuals_from_k4_large,
        "minimum_terminal_residual_margin_from_K_ge_4": min_margin,
        "level_of_minimum_margin": min_margin_k,
        "adjacent_even_fatal_odd_part_audit": adjacent_fatal_oddpart,
        "three_adic_coverage": coverage,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", type=int, default=100_000)
    args = parser.parse_args()
    if args.steps < 0:
        parser.error("--steps must be nonnegative")
    print(json.dumps(run(args.steps), indent=2))


if __name__ == "__main__":
    main()
