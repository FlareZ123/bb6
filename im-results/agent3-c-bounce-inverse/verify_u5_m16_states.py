#!/usr/bin/env python3
"""Independent audit of the five U5 M16 quotient states.

The quotient map is q(n)=n for n<8 and q(n)=8+(n-8) mod 16 otherwise.
For a quotient coordinate r>=8, representatives r and r+16 suffice:
the source transition only uses parity/mod-16 data and shifts by at most 3
in that coordinate; r+16 is the stable large representative, while r
captures the only possible crossing below 8. The quotient transition is
therefore the union of q(nextC(x)) over these representatives.

This is an independent finite computation, not a replacement for the Lean
certificate or its source-simulation proof.
"""
from collections import deque


def q(n: int) -> int:
    return n if n < 8 else 8 + (n - 8) % 16


def reps(r: int) -> tuple[int, ...]:
    return (r,) if r < 8 else (r, r + 16)


def next_c(a: int, k: int, c: int):
    # Exact cases from BB6CLine.nextC.
    if c == 1:
        return (a, k + 1, 0)
    if c == 2:
        return None
    if c == 3:
        return (a, k + 2, 1)
    if c == 0:
        if a == 0:
            return (1, 0, 2 * k + 2)
        if a == 1 and k == 0:
            return (5, 0, 1)
        if a == 1:
            # In the Lean pattern (1,k+1,0), k is one less than
            # the actual second coordinate.
            return (2, 2, 2 * k - 1)
        return (a - 2, 1, 2 * k + 1)

    d = c - 4
    if a == 0:
        if k % 2 == 0:
            return (4 * (k // 2) + 2, 2, d + 1)
        return (4 * (k // 2) + 5, 0, d + 4)
    return (a - 1, k + 1, d + 3)


def quotient_successors(state: tuple[int, int, int]):
    a0, k0, c0 = state
    for a in reps(a0):
        for k in reps(k0):
            for c in reps(c0):
                nxt = next_c(a, k, c)
                if nxt is not None:
                    yield tuple(q(x) for x in nxt)


def reachable_quotient() -> set[tuple[int, int, int]]:
    start = (5, 0, 1)
    seen = {start}
    queue = deque([start])
    while queue:
        state = queue.popleft()
        for nxt in quotient_successors(state):
            if nxt not in seen:
                seen.add(nxt)
                queue.append(nxt)
    return seen


if __name__ == "__main__":
    seen = reachable_quotient()
    targets = {
        (14, 20, 0),
        (10, 19, 0),
        (18, 23, 0),
        (10, 11, 0),
        (18, 15, 0),
    }
    print(f"reachable quotient states: {len(seen)} / {24**3}")
    for state in sorted(targets):
        print(f"{state}: {'REACHABLE' if state in seen else 'absent'}")
    assert len(seen) == 7115
    assert not (targets & seen)
