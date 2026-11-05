"""Exact finite P1 shadow graphs and their automatic affine lifts.

Exploratory computation. The mathematical guarantee is the Lean theorem
finite_base_amplifies, not finite sampling in this program.
"""

from collections import deque
from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class AffineNode:
    cost: int
    base: int
    slope: int


def root(q: int, side: int) -> tuple[int, int]:
    return (0, (12 if side == 0 else 10) * q + 4)


def edges(q: int, side: int, m: int, z: int):
    """All legal exact inverse-shadow edges of (m,z)."""
    t = 0
    while z % (1 << t) == 0:
        v = z >> t
        next_double_plus_one = 16 * q + 8 + side + m + t + v
        if next_double_plus_one % 2:
            yield t, (m + t + 1, (next_double_plus_one - 1) // 2)
        t += 1


def exact_graph(q: int, side: int, limit: int = 200_000) -> set[tuple[int, int]]:
    """Explore the complete exact graph or refuse an unproved size cap."""
    if q < 1 or side not in (0, 1):
        raise ValueError("q must be positive and side must be 0 or 1")
    start = root(q, side)
    seen = {start}
    todo = deque([start])
    while todo:
        m, z = todo.popleft()
        if len(seen) > limit:
            raise OverflowError("Base graph exceeded limit; no certificate")
        for _, child in edges(q, side, m, z):
            if child not in seen:
                seen.add(child)
                todo.append(child)
    return seen


def affine_lift(q: int, side: int):
    """Calculate the theorem's conservative common power-of-two stride."""
    base = exact_graph(q, side)
    M = max(m for m, _ in base)
    K = max(z for _, z in base).bit_length()
    D = M + K + 1
    delta = 1 << D
    coefficient = 12 if side == 0 else 10
    initial = AffineNode(0, root(q, side)[1], coefficient * delta)
    seen = {initial}
    todo = deque([initial])
    while todo:
        state = todo.popleft()
        m, z, slope = state.cost, state.base, state.slope
        assert (m, z) in base and 0 < z < (1 << K)
        assert slope % (1 << (D - m)) == 0
        for t, (mc, zc) in edges(q, side, m, z):
            assert mc <= M and slope % (1 << (t + 1)) == 0
            child = AffineNode(mc, zc, 8 * delta + (slope >> (t + 1)))
            assert child.slope % (1 << (D - mc)) == 0
            if child not in seen:
                seen.add(child)
                todo.append(child)
    return base, seen, M, K, delta


def regression() -> None:
    for q in (29, 30, 31, 33, 61, 94, 158):
        for side in (0, 1):
            base, affine, M, K, delta = affine_lift(q, side)
            for r in (0, 1, 2, 7):
                projected = {
                    (node.cost, node.base + node.slope * r) for node in affine
                }
                expected = exact_graph(q + delta * r, side)
                assert expected == projected, (q, side, r, expected ^ projected)
            print(
                f"PASS q={q} side={side}: base={len(base)} "
                f"affine={len(affine)} M={M} K={K} delta=2^{delta.bit_length()-1}"
            )


if __name__ == "__main__":
    regression()
