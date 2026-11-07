#!/usr/bin/env python3
"""Finite diagnostics for the #623 predecessor-to-ray linear-form bridge.

The transition functions are imported from root_inverse_explorer.py, an exact
iterative mirror of the pinned Cryptids evalA/drainB/highLevelNext equations.
This checks the source-proved bridge inequalities on a finite blank-root
prefix. It is computational evidence only, not an all-time nonhalting proof.
"""

from collections import Counter
from fractions import Fraction

from root_inverse_explorer import eval_a, high_level_next


def pow3_budget(x: int) -> int:
    """Least n such that x < 3**n."""
    n, p = 0, 1
    while p <= x:
        p *= 3
        n += 1
    return n


def predecessor_gaps(previous: tuple[int, int], current: tuple[int, int]):
    """Return branch-specific depth and right/left gap residual bounds."""
    x, y = previous
    a, d = current
    c_right = 1 if d % 2 else 2
    c_left = 9 if d % 2 else 5

    if x == 0:
        return None

    if y % 2 == 1 and x >= y + 5:
        n = pow3_budget(y + 3)
        right = (d - 4 * a - c_right) - (7 * y - 4 * x)
        left = (a - 4 * d - c_left) - (x - 13 * y)
        return "odd-far", n, right, 8 * n + 39, left, 17 * n + 79

    if y % 2 == 0 and x >= y + 3:
        n = pow3_budget(y + 2)
        right = (d - 4 * a - c_right) - (7 * y - 4 * x)
        left = (a - 4 * d - c_left) - (x - 13 * y)
        return "even-far", n, right, 8 * n + 21, left, 17 * n + 52

    if x % 2 == 1 or x == y + 2:
        return None

    if y % 2 == 1:
        n = pow3_budget(x - 1)
        right = (d - 4 * a - c_right) - (7 * x - 4 * y)
        left = (a - 4 * d - c_left) - (y - 13 * x)
        return "odd-near", n, right, 8 * n + 18, left, 17 * n + 14

    n = pow3_budget(x)
    first = eval_a(y + 1 - x, x, 2 * x + 5)
    if first is None:
        raise AssertionError("root trace entered a failed even-near evaluator")
    _, q, _ = first
    if q >= 3**n:
        raise AssertionError("residual block count exceeded the original ternary budget")
    right = (d - 4 * a - c_right) - (7 * x - 4 * y)
    left = (a - 4 * d - c_left) - (y - 13 * x)
    return "even-near", n, right, 14 * n + 12, left, 26 * n + 46


def ray_gap(state: tuple[int, int]):
    """Return (ray, delta, scale) for the four old-cone rays, if applicable."""
    a, d = state
    if d % 2 == 1 and d >= 2 * a + 1:
        t = (d - 2 * a - 1) // 2
        return "right-odd", t - a, a
    if d % 2 == 0 and d >= 2 * a + 2:
        t = (d - 2 * a - 2) // 2
        return "right-even", t - a, a
    if d % 2 == 1 and a >= 2 * d + 9:
        t = a - 2 * d - 9
        return "left-odd", t - 2 * d, d
    if d % 2 == 0 and a >= 2 * d + 5:
        t = a - 2 * d - 5
        return "left-even", t - 2 * d, d
    return None


def diagnostic(steps: int = 10_000) -> dict:
    states = [(0, 7)]
    branch_counts = Counter()
    maxima = {}
    halted = False

    for index in range(steps - 1):
        previous = states[-1]
        current = high_level_next(*previous)
        if current is None:
            halted = True
            break

        result = predecessor_gaps(previous, current)
        if result is not None:
            branch, n, right, right_bound, left, left_bound = result
            if abs(right) > right_bound or abs(left) > left_bound:
                raise AssertionError((index, previous, current, result))
            branch_counts[branch] += 1
            for side, residual, bound in (
                ("right", right, right_bound),
                ("left", left, left_bound),
            ):
                ratio = Fraction(abs(residual), bound)
                key = (branch, side)
                candidate = (ratio, index, previous, current, n, residual, bound)
                if key not in maxima or ratio > maxima[key][0]:
                    maxima[key] = candidate

        states.append(current)

    ray_min = None
    for index, state in enumerate(states[9:], start=9):
        info = ray_gap(state)
        if info is None:
            continue
        ray, delta, scale = info
        ratio = Fraction(delta * delta, scale)
        candidate = (ratio, index, state, ray, delta, scale)
        if ray_min is None or ratio < ray_min[0]:
            ray_min = candidate

    forms = {
        "7d-4a": lambda a, d: 7 * d - 4 * a,
        "7a-4d": lambda a, d: 7 * a - 4 * d,
        "d-13a": lambda a, d: d - 13 * a,
        "a-13d": lambda a, d: a - 13 * d,
    }
    form_min = None
    for index, (a, d) in enumerate(states[16:], start=16):
        for name, form in forms.items():
            value = form(a, d)
            ratio = Fraction(value * value, a + d)
            candidate = (ratio, index, (a, d), name, value, a + d)
            if form_min is None or ratio < form_min[0]:
                form_min = candidate

    return {
        "states": len(states),
        "halted": halted,
        "branch_counts": dict(branch_counts),
        "bridge_max": maxima,
        "minimum_ray_delta_squared_over_scale": ray_min,
        "minimum_four_form_squared_over_mass": form_min,
    }


if __name__ == "__main__":
    report = diagnostic()
    print("Pinned source: google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b")
    print("Finite blank-root states:", report["states"])
    print("Halted in checked prefix:", report["halted"])
    print("Bridge checks by predecessor branch:", report["branch_counts"])
    for (branch, side), item in sorted(report["bridge_max"].items()):
        ratio, index, previous, current, n, residual, bound = item
        print(
            f"  {branch}/{side}: max |error|/bound={ratio} at transition {index}; "
            f"prev={previous}, current={current}, n={n}, error={residual}, bound={bound}"
        )
    print("Minimum old-cone delta^2/scale:", report["minimum_ray_delta_squared_over_scale"])
    print("Minimum four-form L^2/mass:", report["minimum_four_form_squared_over_mass")
