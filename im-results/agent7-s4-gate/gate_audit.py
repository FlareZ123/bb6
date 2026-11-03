#!/usr/bin/env python3
"""Independent exact S4 stepEpoch/weighted-binary-gate regression.

Source: google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b
  BusyBeaver/BB6/Accelerations/
  M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean

No claim of machine-wide nonhalting from any finite test.
"""
from collections import Counter
from itertools import product
from time import perf_counter


def bump_head(xs, n=1):
    """Apply the source bumpHead n times to a tuple of naturals."""
    if n == 0:
        return xs
    return (xs[0] + n, *xs[1:]) if xs else (n - 1,)


def transfer_hl(a, left, right):
    """Exact source right-stack fold with a last-digit-first output."""
    for digit in right:
        a, left = digit, (a, *left)
    return a, left


def step_epoch(a, left, right):
    """Source's well-founded stepEpoch recursion, executed as a loop."""
    while True:
        half = a // 2
        r1 = bump_head(right, half)
        if not left:
            if a <= 1:
                return None
            if a % 2 == 0:
                return transfer_hl(half - 1, (), bump_head(r1, 2))
            a, right = half, (0, *r1)
        else:
            b, *tail = left
            left = tuple(tail)
            if a % 2 == 0:
                return transfer_hl(b + half, left, bump_head(r1, 2))
            a, right = b + half + 1, (0, *r1)


def weighted(left):
    """b_0 + 2*b_1 + 4*b_2 + ..., in source list order."""
    value = 0
    for digit in reversed(left):
        value = digit + 2 * value
    return value


def power_of_two(n):
    return n > 0 and (n & (n - 1)) == 0


def halting_gate(a, left):
    """Derived exact halt criterion for every left/right stack.

    For odd a=2q+1 and n=len(left):
        q + weighted(left) + 2**n = 2**(n+m), for some m>=0.
    The only even-a halting input is a=0 with an empty left stack.
    """
    if a % 2 == 0:
        return a == 0 and not left
    q = a // 2
    weight = q + weighted(left)
    scale = 1 << len(left)
    return weight % scale == 0 and power_of_two(weight // scale + 1)


def audit(max_a=16, digit_max=7, max_len=4, trace_len=100_000):
    cases = Counter()
    t0 = perf_counter()
    for a in range(max_a + 1):
        for n in range(max_len + 1):
            for left in product(range(digit_max + 1), repeat=n):
                predicted = halting_gate(a, left)
                for right in [(0,), (), (2, 7)]:
                    actual = step_epoch(a, left, right) is None
                    assert actual == predicted, (a, left, right, predicted, actual)
                    cases[(n, "halt" if actual else "return")] += 1

    a, left = 3, (0,)
    cycle_counts = Counter()
    visited_halting_congruence = 0
    minimum_len = len(left)
    for i in range(trace_len):
        assert left, ("unexpected empty left stack", i, a)
        if halting_gate(a, left):
            visited_halting_congruence += 1
        next_hub = step_epoch(a, left, (0,))
        assert next_hub is not None, ("actual S4 halt", i, a, left)
        cycle_counts[(a, next_hub[0])] += 1
        a, left = next_hub
        minimum_len = min(minimum_len, len(left))
    print("S4 source =", "c86f15861709b76042998c5211c7b2f83991621b")
    print("synthetic direct stepEpoch comparisons =", sum(cases.values()))
    print("cases by n and outcome =", sorted(cases.items()))
    print("genuine high-level prefix length =", trace_len)
    print("control-state transitions =", sorted(cycle_counts.items()))
    print("genuine reachable halting-gate hits =", visited_halting_congruence)
    print("minimum left-stack length =", minimum_len)
    print("last high-level state =", (a, left[:12], len(left)))
    print("elapsed seconds =", round(perf_counter() - t0, 2))
    print("Finite comparisons PASS; no global divergence claim.")


if __name__ == "__main__":
    audit()
