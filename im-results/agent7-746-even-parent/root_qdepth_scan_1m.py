#!/usr/bin/env python3
"""Exact root t=1 Q-parent scan for machine #746.

This counts reset transitions, not individual Turing-machine tape steps.
The recurrence is the integer reset recurrence used in ROOT-QDEPTH-ALIGNMENT.md.
"""
import argparse
import hashlib
import json


def first_failed_level(h: int) -> int:
    k = max(0, h.bit_length() - 3)
    p = 1 << k
    while h + k + 5 >= 8 * p:
        k += 1
        p <<= 1
    while k > 0 and h + k + 4 < 4 * p:
        k -= 1
        p >>= 1
    return k


def v2(n: int) -> int:
    assert n > 0
    return (n & -n).bit_length() - 1


def run(steps: int) -> dict:
    h = 2
    k = first_failed_level(h)
    p = 1 << k
    even_since_entry = 0

    total_t1 = 0
    sector_t1 = 0
    positive_b = 0
    divisible_8c = 0
    matches = []
    divisible_candidates = []
    max_t = 0
    completed = 0
    halted_at = None

    for step in range(steps):
        if h + k + 4 == 4 * p:
            halted_at = step
            break

        s = h + k
        if s % 2 == 0:
            child = 4 * p + s // 2
            edge_type = "even"
        else:
            raw = 4 * p + s // 2 + 3
            t = v2(raw)
            d = raw >> t
            max_t = max(max_t, t)
            child = (pow(3, t + 1) * d - 5) // 2
            edge_type = "odd"

            if t == 1:
                total_t1 += 1
                if k % 6 in (2, 3):
                    sector_t1 += 1
                    c = 2 * k + 7
                    b = 112 * p - 2 * k - 34 - 18 * h
                    if b > 0:
                        positive_b += 1
                        if b % (8 * c) == 0:
                            divisible_8c += 1
                            ratio = b // (8 * c)
                            exponent = v2(ratio)
                            odd_part = ratio >> exponent
                            candidate = {
                                "transition_index_zero_based": step,
                                "transition_number_one_based": step + 1,
                                "K": k,
                                "source_height": str(h),
                                "same_level_even_resets_since_entry": even_since_entry,
                                "B": str(b),
                                "c": c,
                                "B_over_8c": str(ratio),
                                "v2_ratio": exponent,
                                "odd_part": str(odd_part),
                                "ratio_mod_27": ratio % 27,
                            }
                            divisible_candidates.append(candidate)
                            if ratio == 1 << exponent and exponent % 2 == 1:
                                matches.append(candidate)

        old_k = k
        h = child
        k = first_failed_level(h)
        p = 1 << k
        completed += 1

        if edge_type == "even" and k == old_k:
            even_since_entry += 1
        else:
            even_since_entry = 0

    h_bytes = h.to_bytes((h.bit_length() + 7) // 8, "big")
    return {
        "requested_reset_transitions": steps,
        "completed_reset_transitions": completed,
        "halted_at_zero_based_transition": halted_at,
        "total_t1_sources": total_t1,
        "t1_sources_in_K_mod_6_2_or_3": sector_t1,
        "positive_B_in_surviving_sectors": positive_b,
        "positive_B_divisible_by_8c": divisible_8c,
        "exact_t1_Q_matches": matches,
        "divisible_candidates": divisible_candidates,
        "maximum_odd_reset_exponent_t": max_t,
        "final_K": k,
        "final_height_bit_length": h.bit_length(),
        "final_height_sha256_big_endian": hashlib.sha256(h_bytes).hexdigest(),
        "final_level_deficit_v2": v2(8 * (1 << k) + k - h),
        "final_even_resets_since_entry": even_since_entry,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", type=int, default=1_000_000)
    args = parser.parse_args()
    print(json.dumps(run(args.steps), indent=2, sort_keys=True))
