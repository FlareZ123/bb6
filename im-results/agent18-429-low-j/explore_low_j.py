"""Finite original-table experiments for the #429 low-J chart.

Every tested configuration has the exact infinite J(u,w) tape with finite support.
This script prints finite evidence only. It proves no all-parameter recurrence.
Transition table copied from BB429PhysicalFrontier.prefix11.
"""

from __future__ import annotations

# state A-F encoded 0-5; value (next_state, write_one, signed_head_move).
TABLE = {
    (0, 0): (1, 1, 1), (0, 1): (5, 0, -1),
    (1, 0): (2, 1, 1), (1, 1): (0, 1, 1),
    (2, 0): (3, 0, 1), (2, 1): (1, 0, 1),
    (3, 0): (4, 1, -1),
    (4, 0): (0, 0, -1), (4, 1): (4, 1, -1),
    (5, 0): (3, 1, 1), (5, 1): (0, 1, -1),
}


def j_ones(u: int, w: int) -> set[int]:
    return {
        x for x in range(-2 * u - 6, w + 4)
        if (x <= w + 1 and not (-2 * u <= x < 0 and x % 2 == 0))
        or x == w + 3
    }


def predicted(r: int, u: int) -> tuple[int, int, int, int]:
    """(raw time, successor J-u, successor J-w, absolute head)."""
    k, rem = divmod(r, 4)
    if rem == 2:
        return (
            4*u*u + (14-16*k)*u + 16*k*k-10*k+61,
            0, 4*u+8-4*k, -2*u-3,
        )
    if rem == 0 and k >= 1:
        return (
            4*u*u + (22-16*k)*u + 16*k*k-26*k+261,
            11, 4*u-4*k-2, 9-2*u,
        )
    if rem == 1 and k >= 1:
        return (
            4*u*u + (14-16*k)*u + 16*k*k-6*k+60,
            2*k+4, 4*u-8*k-2, -2*u+4*k+4,
        )
    if rem == 3 and k >= 1:
        return (
            4*u*u + (6-16*k)*u + 16*k*k+26*k+146,
            2*k+9, 4*u-8*k-10, -2*u+4*k+10,
        )
    # The offset r=3 has a separate simpler boundary return.
    if r == 3:
        return (4*u*u+6*u+26, 0, 4*u+2, -2*u-2)
    raise ValueError(f"r={r} not covered")


def run_raw(u: int, w: int, steps: int) -> tuple[int, int, set[int]]:
    ones = j_ones(u, w)
    head = 0
    state = 0
    for _ in range(steps):
        move = TABLE.get((state, int(head in ones)))
        if move is None:
            raise AssertionError(f"unexpected halt from J({u},{w})")
        state, value, direction = move
        if value:
            ones.add(head)
        else:
            ones.discard(head)
        head += direction
    return (state, head, ones)


def main() -> None:
    tested = 0
    for r in range(2, 35):
        lo = max(1, (r + 1) // 2)
        for u in range(lo, min(36, lo + 17)):
            t, target_u, target_w, target_head = predicted(r, u)
            if target_w < 0 or t < 0:
                continue
            state, head, ones = run_raw(u, 2*u-r, t)
            target = {target_head + x for x in j_ones(target_u, target_w)}
            if (state, head, ones) != (0, target_head, target):
                raise AssertionError(
                    f"failure r={r}, u={u}, time={t}: state={state}, head={head}"
                )
            tested += 1
    print(f"Original source table: {tested} low-J tests passed; finite evidence only.")


if __name__ == "__main__":
    main()
