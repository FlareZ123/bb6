"""Independent exhaustive checker for two mixed96 reverse-closed arithmetic cores.

This is computational evidence, not a Lean kernel certificate.
Assumptions: Agent11's nextC branches as transcribed here; mixed96's
source-sound abstraction was separately checked by Agent41's Lean bridge.
"""

from collections import deque

A_SIZE = K_SIZE = 96
C_SIZE = 50
N = A_SIZE * K_SIZE * C_SIZE


def index(a: int, k: int, c: int) -> int:
    return (a * K_SIZE + k) * C_SIZE + c


def coords(i: int) -> tuple[int, int, int]:
    return i // (K_SIZE * C_SIZE), i // C_SIZE % K_SIZE, i % C_SIZE


def next_c(a: int, k: int, c: int) -> tuple[int, int, int] | None:
    if c == 1:
        return a, k + 1, 0
    if c == 2:
        return None
    if c == 3:
        return a, k + 2, 1
    if c == 0:
        if a == 0:
            return 1, 0, 2 * k + 2
        if a == 1:
            return (5, 0, 1) if k == 0 else (2, 2, 2 * k - 1)
        return a - 2, 1, 2 * k + 1
    if a == 0:
        return (2 * k + 2, 2, c - 3) if k % 2 == 0 else (2 * k + 3, 0, c)
    return a - 1, k + 1, c - 1


def quotient(t: tuple[int, int, int]) -> int:
    a, k, c = t
    return index(a % 96, k % 96, c if c < 2 else 2 + (c - 2) % 48)


def successors(a: int, k: int, c: int):
    for aa in (a, a + 96):
        for kk in (k, k + 96):
            for cc in ((c,) if c < 2 else (c, c + 48)):
                t = next_c(aa, kk, cc)
                if t is not None:
                    yield quotient(t)


def core_a(a: int, k: int, c: int) -> bool:
    if c == 0:
        return (a % 48, k % 24) in ((18, 23), (20, 0), (42, 11))
    if c == 1:
        return (a % 48, k % 24) in ((18, 22), (20, 23), (42, 10))
    d = c - 2
    x, y = (a - d) % 96, (k + d) % 96
    return (
        (x % 48 == 2 and y % 24 == 5)
        or (x, y) in ((12, 29), (60, 77))
        or (x % 48 == 17 and y % 24 == 21)
        or (x % 48 == 19 and y % 48 in (0, 22, 46))
        or (x % 48 == 26 and y % 24 == 17)
        or (x % 48 == 41 and y % 24 == 9)
    )


def core_b(a: int, k: int, c: int) -> bool:
    if c == 0:
        return (a % 48, k % 24) in ((4, 16), (18, 7), (42, 19))
    if c == 1:
        return (a % 48, k % 24) in ((4, 15), (18, 6), (42, 18))
    d = c - 2
    x, y = (a - d) % 96, (k + d) % 96
    return (
        (x % 48 == 3 and y % 24 == 14)
        or (x % 48 == 10 and y % 24 == 9)
        or (x % 48 == 17 and y % 24 == 5)
        or (x % 48 == 19 and y % 48 == 32)
        or (x, y) in ((28, 77), (76, 29))
        or (x % 48 == 34 and y % 24 == 21)
        or (x % 48 == 41 and y % 24 == 17)
    )


def reverse_closure(target: int, reverse: list[list[int]]) -> bytearray:
    visited = bytearray(N)
    visited[target] = 1
    queue = deque([target])
    while queue:
        for pred in reverse[queue.popleft()]:
            if not visited[pred]:
                visited[pred] = 1
                queue.append(pred)
    return visited


def verify() -> None:
    core_flags = [
        bytearray(core_a(*coords(i)) for i in range(N)),
        bytearray(core_b(*coords(i)) for i in range(N)),
    ]
    assert [sum(f) for f in core_flags] == [2256, 2256]
    origin = index(5, 0, 1)
    assert not core_flags[0][origin] and not core_flags[1][origin]
    assert not any(x and y for x, y in zip(*core_flags))

    reverse = [[] for _ in range(N)]
    all_edges = 0
    for u in range(N):
        for v in successors(*coords(u)):
            reverse[v].append(u)
            all_edges += 1
            for flags in core_flags:
                assert not flags[v] or flags[u], (coords(u), coords(v))
    assert all_edges == 3575808

    for j, targets in enumerate(
        (((13, 31, 0), (61, 79, 0)), ((29, 79, 0), (77, 31, 0)))
    ):
        core = core_flags[j]
        for a, k, c in targets:
            target = index(a, k, c)
            feeder1 = index(a, k - 1, 1)
            feeder2 = index(a, k - 3, 3)
            assert set(reverse[target]) == {feeder1}
            assert set(reverse[feeder1]) == {feeder2}
            assert core[feeder2]
            ancestors = reverse_closure(target, reverse)
            expected = bytearray(core)
            expected[target] = expected[feeder1] = 1
            assert ancestors == expected
            assert sum(ancestors) == 2258
            print(f"target {(a,k,c)}: 2258 ancestors; two-step feeder in core {j + 1}")

    # Independent forward check of the known mixed96 census.
    seen = bytearray(N)
    seen[origin] = 1
    queue = deque([origin])
    forward_edges = 0
    while queue:
        for v in successors(*coords(queue.popleft())):
            forward_edges += 1
            if not seen[v]:
                seen[v] = 1
                queue.append(v)
    assert sum(seen) == 260672
    assert forward_edges == 2022544
    assert not any(seen[i] and (core_flags[0][i] or core_flags[1][i]) for i in range(N))
    print(f"PASS: {N} vertices; {all_edges} abstract edges; "
          f"{sum(seen)} forward-reached; {forward_edges} reached edges")
    print("PASS: two disjoint predecessor-closed cores of 2256 states each")


if __name__ == "__main__":
    verify()
