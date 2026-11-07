"""Reproduce the sharp terminal-balance interval scan for machine #623.

Imports the exact Python mirror in root_inverse_explorer.py. This is finite
computational evidence, not an all-time proof.

The source pin and transition transcription are documented in that module.
"""


from root_inverse_explorer import eval_a, high_level_next


def pow3_budget(x: int) -> int:
    """Least k with 3**k > x."""
    k, p = 0, 1
    while p <= x:
        p *= 3
        k += 1
    return k


def final_drain_input(a: int, d: int):
    """Return (branch, (x,b,y)) for the final drain in highLevelNext."""
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


def diagnostic(steps: int = 10_000) -> dict:
    state = (0, 7)
    old_candidates = []
    new_candidates = []
    closest = None
    checked = 0
    halted = False

    for i in range(steps):
        a, d = state
        if i >= 9:
            branch, drain = final_drain_input(a, d)
            if drain is not None:
                x, b, y = drain
                n = pow3_budget(b)
                g = x - y - 3 * b

                # Previous envelope: aa >= x-b, dd <= y+7b,
                # aa <= x+n, dd >= y+3b.
                old_mass = x + y + 7 * b + n
                old_k = pow3_budget(2 * old_mass + 5)
                old_lo = -(n + old_k + 5)
                old_hi = 5 * b + old_k + 5
                if old_lo <= g <= old_hi:
                    old_candidates.append((i, state, branch, drain, g,
                                           (old_lo, old_hi)))

                # New sharp envelope:
                # x-(n+1) <= aa <= x+n
                # y+3b <= dd <= y+3b+4n+2.
                new_mass = x + y + 3 * b + 5 * n + 2
                new_k = pow3_budget(2 * new_mass + 5)
                new_lo = -(n + new_k + 4)
                new_hi = 5 * n + new_k + 7
                margin = (new_lo - g if g < new_lo
                          else g - new_hi if g > new_hi else 0)
                checked += 1
                candidate = (i, state, branch, drain, g,
                             (new_lo, new_hi), n, new_k)
                if margin == 0:
                    new_candidates.append(candidate)
                if closest is None or margin < closest[0]:
                    closest = (margin, *candidate)

        state = high_level_next(*state)
        if state is None:
            halted = True
            break

    return {
        "states_checked": checked,
        "halted": halted,
        "old_candidates": len(old_candidates),
        "new_candidates": len(new_candidates),
        "closest_new_interval_miss": closest,
        "old_examples": old_candidates[:5],
    }


if __name__ == "__main__":
    print(diagnostic())
