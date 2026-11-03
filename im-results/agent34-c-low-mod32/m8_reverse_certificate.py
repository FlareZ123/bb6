"""Reproducible finite reverse-cone experiment for Machine C's m=8 low gate.

The arithmetic inversion implements the original SectionAllInverse equations.
All selected edges are replayed by an independently spelled-out secNext.
Formal completeness of the arithmetic grammar is proved upstream in Lean:
BB6.Agent46.section_preimage_all_iff. This Python run is not a Lean certificate.
No files are written.
"""

from collections import Counter, deque
import hashlib
import json


def bounce(k: int, c: int) -> tuple[int, tuple[int, int] | None]:
    """Exact original Agent46 BounceCalc section recursion, iteratively unwound."""
    elapsed = 0
    while True:
        if c < 4:
            return elapsed, None
        if k % 2:
            if c <= 2 * k + 6:
                return elapsed + c, (2 * k + 6 - c, c)
            elapsed += 2 * k + 4
            c, k = c - (2 * k + 3), 2 * k + 3
        else:
            if c == 4:
                return elapsed + 2, (2 * k + 2, 3)
            if c == 5:
                return elapsed + 2, None
            if c <= 2 * k + 8:
                return elapsed + c - 3, (2 * k + 8 - c, c - 1)
            elapsed += 2 * k + 3
            c, k = c - (2 * k + 5), 2 * k + 4


def sec_next(a: int, k: int) -> tuple[int, int] | None:
    """Original Agent46 FastSectionDef transition, preserving every exception."""
    if a == 0:
        if k == 0:
            return None
        if k == 1:
            return 0, 4
        return bounce(1, 2 * k + 1)[1]
    if a == 1:
        if k == 0:
            return 5, 1
        if k == 1:
            return 2, 3
        if k == 2:
            return 2, 5
        if k == 3:
            return 0, 7
        return bounce(4, 2 * k - 3)[1]
    if k == 0:
        return a - 2, 2
    if 2 * k <= a:
        return a - 2 * k, 2 * k + 2
    return bounce(a - 1, 2 * k - a + 3)[1]


def parents(x: int, y: int) -> list[tuple[int, int]]:
    """Solve ALL branches of the proven source inverse grammar at target (x,y)."""
    found: set[tuple[int, int]] = set()

    def add(a: int, k: int) -> None:
        if a >= 0 and k >= 0:
            assert sec_next(a, k) == (x, y), ((a, k), (x, y))
            found.add((a, k))

    if (x, y) == (0, 4):
        add(0, 1)

    v = x + y
    if y >= 4 and v >= 8 and v.bit_count() == 1:
        n = v.bit_length() - 4
        if v == (8 << n):
            two_k = x + 2 * y - 9 - 3 * n
            if two_k >= 4 and two_k % 2 == 0:
                add(0, two_k // 2)

    for k, target in [(0, (5, 1)), (1, (2, 3)),
                      (2, (2, 5)), (3, (0, 7))]:
        if target == (x, y):
            add(1, k)

    w = x + 6 if y == 3 else x + y + 1
    if (y == 3 or y >= 5) and w >= 16 and w.bit_count() == 1:
        n = w.bit_length() - 5
        if w == (16 << n):
            two_k = (x - 3 - 3 * n) if y == 3 else x + 2 * y - 11 - 3 * n
            if two_k >= 8 and two_k % 2 == 0:
                add(1, two_k // 2)

    if y == 2:
        add(x + 2, 0)
    if y >= 4 and y % 2 == 0:
        # Direct branch; assert checks its a>=2, k>0, 2k<=a guards.
        a, k = x + y - 2, (y - 2) // 2
        add(a, k)

    if y >= 4:
        for n in range(v.bit_length() + 1):
            power = 1 << n
            if v % power:
                break
            q = v // power
            if q < 8:
                break
            if q % 2:
                continue
            a = (q - 4) // 2
            if a < 2 or a % 2:
                continue
            two_k = x + 2 * y - a - 7 - 3 * n
            if two_k >= 0 and two_k % 2 == 0:
                k = two_k // 2
                if k > 0 and 2 * k > a:
                    add(a, k)

    if y == 3 or y >= 5:
        for n in range(w.bit_length() + 1):
            power = 1 << n
            if w % power:
                break
            q = w // power
            if q < 12:
                break
            if q % 2:
                continue
            a = (q - 6) // 2
            if a < 3 or a % 2 == 0:
                continue
            two_k = (x - a + 1 - 3 * n) if y == 3 else x + 2 * y - a - 7 - 3 * n
            if two_k >= 0 and two_k % 2 == 0:
                k = two_k // 2
                if k > 0 and 2 * k > a:
                    add(a, k)

    return sorted(found)


def forbidden(state: tuple[int, int]) -> tuple[str, ...]:
    """Previously proved original-source global blank-section exclusions."""
    a, k = state
    if state == (5, 1):
        return ()
    reasons = []
    if k == 0:
        reasons.append("right_zero")
    if a % 4 == 0 and k % 4 == 1:
        reasons.append("zeroone")
    if k % 2 and (a + k) % 4 == 2:
        reasons.append("sum_two")
    if k >= 5 and k % 2 and (a + k) % 4 == 1:
        reasons.append("odd_image_sum_one")
    if a % 4 == 1 and k % 8 == 0:
        reasons.append("one8")
    if a % 2 and k % 2 and (a + k) % 8 == 4 and (a + 3 * k) % 16 == 14:
        reasons.append("odd_special")
    return tuple(reasons)


def main() -> None:
    # Independent, small exhaustive regression over every tested forward edge.
    checked = 0
    for a in range(250):
        for k in range(250):
            target = sec_next(a, k)
            if target is not None:
                assert (a, k) in parents(*target), (a, k, target)
                checked += 1

    m = 8
    k_gate = (1 << (2 * m + 3)) - 3 * m - 4
    target = (1, k_gate)
    start = (5, 1)
    q = deque([target])
    seen = {target}
    internal_edges = []
    excluded_edges = []

    while q:
        state = q.popleft()
        for parent in parents(*state):
            reasons = forbidden(parent)
            if reasons:
                excluded_edges.append((state, parent, reasons))
                continue
            internal_edges.append((state, parent))
            if parent not in seen:
                seen.add(parent)
                q.append(parent)

    assert start not in seen
    assert len(seen) == 41, len(seen)
    assert len(internal_edges) == 40, len(internal_edges)
    assert len(excluded_edges) == 15, len(excluded_edges)
    assert not any(sec_next(*p) != target for v, p in internal_edges if v == target)
    reasons = Counter(name for _, _, names in excluded_edges for name in names)
    digest_input = json.dumps(
        {"states": sorted(seen), "internal": sorted(internal_edges),
         "excluded": sorted(excluded_edges)},
        separators=(",", ":"), sort_keys=True,
    ).encode()
    print(f"Original transition regression: {checked} successful edges / 62,500 input pairs")
    print(f"Gate m={m}, target={target}; reverse states={len(seen)}, "
          f"internal edges={len(internal_edges)}, proven-guard edges={len(excluded_edges)}")
    print("Boundary guard counts:", dict(sorted(reasons.items())))
    print("SHA256 of canonical sorted reverse witness:", hashlib.sha256(digest_input).hexdigest())
    for state in sorted(seen):
        print("STATE", *state)
    for node, parent, names in sorted(excluded_edges):
        print("GUARD", *node, "FROM", *parent, ",".join(names))
    print("STATUS: reproducible computational reverse witness; kernel proof pending")


if __name__ == "__main__":
    main()
