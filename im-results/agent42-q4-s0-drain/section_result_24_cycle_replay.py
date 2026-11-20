#!/usr/bin/env python3
"""End-to-end finite replay of the 24-class S1 section dispatcher.

Reuses the original-TM2 simulator and exact S1 tape encoding from
m2_zero_residue_replay.py. Each tested run executes the actual machine through
N consecutive source increments, while independently accumulating the
sectionResult recurrence and its proposed exact cost. It then compares the
complete tape, state, and head with the predicted endpoint.

This is finite computational corroboration, not a proof of the universal
Lean theorem sectionResult_run_complete.
"""

from m2_zero_residue_replay import Config, run, s1_config, same_config, v2


def proposed_increment_cost(m: int, n: int, a: int, b: int) -> int:
    return (6 * (4 ** b) + 42 * (2 ** b) + 15 + 4 * m
            + 12 * (a + v2(n)) - 9 * b)


def replay_section(N: int, initial_m: int, initial_a: int,
                   initial_b: int, require_full_cycle: bool = True
                   ) -> tuple[int, int]:
    assert N > 0 and initial_a > 0 and initial_b >= 0
    L = max(4, N.bit_length())
    assert L >= 4 and N < (1 << L)

    n, m, a, b, head = N, initial_m, initial_a, initial_b, 0
    source = s1_config(L, n, m, a, 0, b, head)
    visited_classes: set[tuple[int, int]] = set()
    total_steps = 0

    for _ in range(N):
        visited_classes.add((m, n % 8))
        old_b = b
        total_steps += proposed_increment_cost(m, n, a, old_b)
        run(source, proposed_increment_cost(m, n, a, old_b))

        a += old_b + (1 if m == 0 else 2)
        b = (1 << old_b) - 1
        m = (m + 2) % 3
        n -= 1
        head += 5 + 3 * old_b

    if require_full_cycle and len(visited_classes) != 24:
        raise AssertionError(
            f"expected all 24 (marker,residue) classes, got "
            f"{len(visited_classes)} for N={N}, m={initial_m}"
        )

    target = s1_config(L, 0, m, a, 0, b, head)
    if not same_config(source, target):
        raise AssertionError(
            f"section endpoint mismatch: N={N}, m={initial_m}, "
            f"a={initial_a}, b={initial_b}; "
            f"got=({source.state},{source.head},{len(source.ones)} ones), "
            f"expected=({target.state},{target.head},{len(target.ones)} ones)"
        )
    return total_steps, len(visited_classes)


def check_cycles() -> tuple[int, int]:
    cases = 0
    total_steps = 0
    for N in (24, 48):
        for m in range(3):
            for a in (1, 2, 3):
                for b in (0, 1):
                    steps, classes = replay_section(N, m, a, b)
                    assert classes == 24
                    cases += 1
                    total_steps += steps
    return cases, total_steps


def check_growing_right_prefixes() -> tuple[int, int]:
    # b=2 produces 2 -> 3 -> 7 -> 127; b=3 produces 3 -> 7 -> 127.
    # Stop before attempting the next, astronomically larger increment.
    cases = 0
    total_steps = 0
    for m in range(3):
        for a in (1, 2):
            for b, N in ((2, 3), (3, 2)):
                steps, _ = replay_section(N, m, a, b,
                                          require_full_cycle=False)
                cases += 1
                total_steps += steps
    return cases, total_steps


if __name__ == "__main__":
    cycle_cases, cycle_steps = check_cycles()
    growth_cases, growth_steps = check_growing_right_prefixes()
    cases = cycle_cases + growth_cases
    steps = cycle_steps + growth_steps
    print(f"TM63 section replay: PASS ({cases} cases)")
    print(f"Full-cycle cases: {cycle_cases}; all 24 classes visited in each")
    print(f"Growing-right prefix cases: {growth_cases}; final right counter 127")
    print(f"Exact simulated transitions: {steps}")
