"""Finite diagnostics for source BB6 #623 two-step filters.

The formal results live in the Lean files. This finite script proves no
all-time statement and is intended only for research prioritization.
"""
from collections import Counter


def evaluate(a, k, m):
    while True:
        q, r = divmod(k, 3)
        if r == 2:
            return a + 1, q, m
        if a == 0:
            return None if r == 0 else (0, q, m)
        if r == 0:
            return a - 1, q, m + 2
        a, k, m = a - 1, q, m + 2 * q + 3


def drain(a, b, d):
    while b:
        transformed = evaluate(a, b - 1, d + 2 * b + 3)
        if transformed is None:
            return None
        a, next_b, d = transformed
        assert next_b < b
        b = next_b
    return a, d


def transition(a, d):
    if a == 0:
        return drain(d + 1, 2, 2) if d % 2 else (d, 7)
    if d % 2 and a >= d + 5:
        return drain(a - d - 5, d + 3, 5)
    if d % 2 == 0 and a >= d + 3:
        return drain(a - d - 2, d + 2, 2)
    if a % 2:
        return None
    if a == d + 2:
        return drain(0, a, 2)
    if d % 2:
        return drain(d + 4 - a, a - 1, 3)
    transformed = evaluate(d + 1 - a, a, 2 * a + 5)
    return None if transformed is None else drain(*transformed)


def ternary_budget(b):
    k, bound = 0, 1
    while bound <= b:
        k, bound = k + 1, 3 * bound
    return k


def near_gate(a, d):
    if a == 0 or a % 2:
        return False
    if d % 2:
        if a < d + 5:
            k = ternary_budget(a - 1)
            return 2 * d + 2 * k + 16 <= 5 * a
        k = ternary_budget(d + 3)
        return 2 * a + 2 * k <= 5 * d + 16
    if a <= d:
        k = ternary_budget(a)
        return 2 * d + 2 * k + 7 <= 4 * a
    if a == d + 2:
        k = ternary_budget(a)
        return 2 * k + 6 <= 3 * a
    k = ternary_budget(d + 2)
    return 2 * a + 2 * k <= 5 * d + 4


def far_left(a, d):
    return a > 0 and a >= 16 * d + (68 if d % 2 else 44)


def far_right(a, d):
    return a > 0 and a % 2 == 0 and d >= (16 * a if d % 2 else 14 * a + 24)


def main():
    state = (0, 7)
    categories = Counter()
    initial = []
    for index in range(5000):
        a, d = state
        assert a % 2 == 0
        if index < 5:
            initial.append(state)
        group = ("zero" if a == 0 else "gate" if near_gate(a, d)
                 else "far_left" if far_left(a, d)
                 else "far_right" if far_right(a, d) else "uncovered")
        categories[group] += 1
        state = transition(a, d)
        assert state is not None, f"halt at section {index}"
    assert initial == [(0, 7), (6, 14), (6, 31), (26, 26), (2, 83)]
    assert categories == {"zero": 1, "gate": 1924, "far_left": 232,
                          "far_right": 433, "uncovered": 2410}
    print("First 5000 source-mirrored visits:", dict(sorted(categories.items())))
    print("Uncovered:", categories["uncovered"], "of 5000")
    print("Finite trace only; no nonhalting conclusion.")


if __name__ == "__main__":
    main()
