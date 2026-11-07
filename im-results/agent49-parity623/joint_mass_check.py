#!/usr/bin/env python3
"""Reproduce finite checks for the sharp #623 drain joint-mass bound.

The transition functions are imported from root_inverse_explorer.py, the
iterative mirror of the pinned Cryptids evalA/drainB/highLevelNext equations.
All tests are finite diagnostics; the universal statement is proved in
JointMassSource.lean.
"""

from collections import Counter
import random

from root_inverse_explorer import drain_b, eval_a, high_level_next


def pow3_budget(x: int) -> int:
    """Least n such that x < 3**n."""
    n, power = 0, 1
    while power <= x:
        power *= 3
        n += 1
    return n


def final_drain_input(a: int, d: int):
    """Return (branch, final B-drain input) for highLevelNext(D(a,d))."""
    if a == 0:
        if d % 2:
            return "axis-odd", (d + 1, 2, 2)
        return "axis-even", None
    if d % 2 == 1 and a >= d + 5:
        return "far-left-odd", (a - d - 5, d + 3, 5)
    if d % 2 == 0 and a >= d + 3:
        return "far-left-even", (a - d - 2, d + 2, 2)
    if a % 2 == 1:
        return "odd-a", None
    if a == d + 2:
        return "diagonal-even", (0, a, 2)
    if d % 2 == 1:
        return "right-odd", (d + 4 - a, a - 1, 3)
    first = eval_a(d + 1 - a, a, 2 * a + 5)
    if first is None:
        return "right-even-fail", None
    return "right-even", first


def check_mass_bound(samples: int = 200_000) -> dict:
    """Check small exhaustive and seeded random successful drain inputs."""
    exhaustive_successes = 0
    for a in range(80):
        for b in range(80):
            n = pow3_budget(b)
            for d in range(5):
                out = drain_b(a, b, d)
                if out is None:
                    continue
                aa, dd = out
                exhaustive_successes += 1
                assert aa + dd <= a + d + 3 * b + 3 * n + 1

    rng = random.Random(623)
    random_successes = 0
    for _ in range(samples):
        a = rng.randrange(10_000)
        b = rng.randrange(10_000)
        d = rng.randrange(10_000)
        n = pow3_budget(b)
        out = drain_b(a, b, d)
        if out is None:
            continue
        aa, dd = out
        random_successes += 1
        assert aa + dd <= a + d + 3 * b + 3 * n + 1

    sharp_witnesses = []
    block = 2
    for n in range(10):
        depth = n + 1
        d = 17 + n
        out = drain_b(n + 2, block, d)
        expected = (0, d + 3 * block + 4 * n + 6)
        assert block < 3**depth
        assert out == expected
        assert sum(out) == (n + 2) + d + 3 * block + 3 * depth + 1
        sharp_witnesses.append((n, block, depth, out))
        block = 3 * block + 1

    return {
        "exhaustive_successes": exhaustive_successes,
        "random_trials": samples,
        "random_successes": random_successes,
        "sharp_witnesses": sharp_witnesses,
    }


def root_balance_scan(steps: int = 10_000) -> dict:
    """Compare componentwise and joint-mass terminal balance intervals."""
    state = (0, 7)
    checked = 0
    componentwise_candidates = []
    joint_candidates = []
    k_reductions = []
    closest_componentwise = None
    closest_joint = None

    for index in range(steps):
        a, d = state
        if index >= 9:
            branch, drain = final_drain_input(a, d)
            if drain is not None:
                x, b, y = drain
                n = pow3_budget(b)
                g = x - y - 3 * b

                componentwise_mass = x + y + 3 * b + 5 * n + 2
                componentwise_k = pow3_budget(2 * componentwise_mass + 5)
                componentwise_interval = (
                    -(n + componentwise_k + 4),
                    5 * n + componentwise_k + 7,
                )

                joint_mass = x + y + 3 * b + 3 * n + 1
                joint_k = pow3_budget(2 * joint_mass + 5)
                joint_interval = (
                    -(n + joint_k + 4),
                    5 * n + joint_k + 7,
                )

                out = drain_b(x, b, y)
                assert out is not None
                aa, dd = out
                assert aa + dd <= joint_mass

                def margin(interval):
                    lo, hi = interval
                    return lo - g if g < lo else g - hi if g > hi else 0

                componentwise_margin = margin(componentwise_interval)
                joint_margin = margin(joint_interval)
                checked += 1
                if componentwise_margin == 0:
                    componentwise_candidates.append((index, state, branch, drain, g))
                if joint_margin == 0:
                    joint_candidates.append((index, state, branch, drain, g))
                if closest_componentwise is None or componentwise_margin < closest_componentwise[0]:
                    closest_componentwise = (
                        componentwise_margin, index, state, branch, drain, g,
                        componentwise_interval, n, componentwise_k,
                    )
                if closest_joint is None or joint_margin < closest_joint[0]:
                    closest_joint = (
                        joint_margin, index, state, branch, drain, g,
                        joint_interval, n, joint_k,
                    )
                if joint_k < componentwise_k:
                    k_reductions.append((index, componentwise_k, joint_k,
                                         componentwise_mass, joint_mass))

        state = high_level_next(*state)
        if state is None:
            break

    return {
        "states_with_final_drain": checked,
        "componentwise_interval_candidates": len(componentwise_candidates),
        "joint_interval_candidates": len(joint_candidates),
        "closest_componentwise_miss": closest_componentwise,
        "closest_joint_miss": closest_joint,
        "K_reductions": k_reductions,
    }




def terminal_ratio4_scan(steps: int = 10_000) -> dict:
    """Check the ratio-4 necessary condition obtained by subtracting ray gaps."""
    state = (0, 7)
    checked = 0
    candidates = []
    branch_min_margin = {}

    for index in range(steps):
        x, y = state
        if index >= 9:
            branch, drain = final_drain_input(x, y)
            if drain is not None:
                p, b, r = drain
                if branch == "far-left-odd":
                    n = pow3_budget(b)
                    mass = x + 2 * y + 10 + 3 * n
                    bound = pow3_budget(2 * mass + 5) + 5 * n + 29
                    gap = 4 * y - x
                elif branch == "far-left-even":
                    n = pow3_budget(b)
                    mass = x + 2 * y + 7 + 3 * n
                    bound = pow3_budget(2 * mass + 5) + 5 * n + 20
                    gap = 4 * y - x
                elif branch == "right-odd":
                    n = pow3_budget(b)
                    mass = y + 2 * x + 5 + 3 * n
                    bound = pow3_budget(2 * mass + 5) + 5 * n + 12
                    gap = 4 * x - y
                elif branch == "right-even":
                    n = pow3_budget(x)
                    mass = y + 2 * x + 5 + 3 * n
                    bound = pow3_budget(2 * mass + 5) + 8 * n + 17
                    gap = 4 * x - y
                else:
                    state = high_level_next(*state)
                    if state is None:
                        break
                    continue

                checked += 1
                margin = abs(gap) - bound
                out = drain_b(p, b, r)
                assert out is not None
                if margin <= 0:
                    candidates.append({
                        "index": index,
                        "branch": branch,
                        "state": (x, y),
                        "gap": gap,
                        "bound": bound,
                        "output": out,
                        "output_has_successor": high_level_next(*out) is not None,
                    })
                old = branch_min_margin.get(branch)
                if old is None or margin < old[0]:
                    branch_min_margin[branch] = (margin, index, (x, y), gap, bound)

        state = high_level_next(*state)
        if state is None:
            break

    return {
        "states_with_final_drain": checked,
        "ratio4_candidates": candidates,
        "minimum_margins_by_branch": branch_min_margin,
    }

if __name__ == "__main__":
    print("Joint-mass finite checks:", check_mass_bound())
    print("Root balance comparison:", root_balance_scan())
    print("Terminal ratio-4 scan:", terminal_ratio4_scan())
