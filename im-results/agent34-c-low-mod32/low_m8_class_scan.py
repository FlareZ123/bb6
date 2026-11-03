"""Finite empirical study of all m=8+32*t for 0<=t<256.

Run with Python 3.10+ from its own directory. Imports the source-exact
Python original-section inversion and source-certified obstruction predicates.
No file writes, no cutoff accepted as an exclusion, and no Lean theorem.
"""
from collections import Counter, deque
from time import monotonic
from m8_reverse_certificate import forbidden, parents


def explore(m: int, cap: int = 200_000) -> tuple[int, int, int]:
    target = (1, (1 << (2 * m + 3)) - 3 * m - 4)
    q = deque([(target, 0)])
    seen = {target}
    max_depth = 0
    while q and len(seen) < cap:
        state, depth = q.popleft()
        max_depth = max(max_depth, depth)
        for parent in parents(*state):
            if forbidden(parent):
                continue
            if parent not in seen:
                seen.add(parent)
                q.append((parent, depth + 1))
    return len(seen), max_depth, len(q)


def main() -> None:
    start = monotonic()
    status = Counter()
    maximum_size = (0, -1)
    maximum_depth = (0, -1)
    pending = []

    for m in range(8, 8 + 32 * 256, 32):
        size, depth, queued = explore(m)
        status["complete" if not queued else "capped"] += 1
        if size > maximum_size[0]:
            maximum_size = (size, m)
        if depth > maximum_depth[0]:
            maximum_depth = (depth, m)
        if queued:
            pending.append((m, size, queued))

    print("Sampled m = 8,40,...,8168, count", sum(status.values()))
    print("Complete under existing blank-obstruction filters:", status["complete"])
    print("Capped (unknown):", status["capped"], pending)
    print("Largest surviving reverse cone:", maximum_size)
    print("Deepest backward node:", maximum_depth)
    print("Elapsed seconds:", round(monotonic() - start, 2))
    assert status == Counter({"complete": 256})
    assert maximum_size == (144023, 3400)
    assert maximum_depth == (1551, 3400)
    print("These are empirical finite enumerations, never a universal proof.")


if __name__ == "__main__":
    main()
