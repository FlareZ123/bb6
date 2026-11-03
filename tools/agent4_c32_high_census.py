"""Exact, root-preserving M16→M32 high-gateway quotient census for Machine C.

Recomputes the Agent43 B=8/M=32 graph with its published interpreter;
independently computes the matching B=8/M=16 quotient. This is a finite
certificate-input audit, not by itself a mathematical reachability proof.
Original mathematical soundness is via kernel-tested CFull32 and source bridge.
"""
from collections import deque

from agent43_c32_certificate import graph as kernel_graph, nxt


def quotient(modulus: int) -> tuple[int, int, set[tuple[int, int]]]:
    width = 8 + modulus

    def q(x: int) -> int:
        return x if x < 8 else 8 + (x - 8) % modulus

    def encode(a: int, k: int, c: int) -> int:
        return (a * width + k) * width + c

    if modulus == 32:
        seen = kernel_graph()  # Runs full original-source Agent43 B8/M32 closure.
        expected_edges = 189834
    else:
        seen = bytearray(width**3)
        start = encode(5, 0, 1)
        seen[start] = 1
        pending = deque([start])
        edges = 0
        while pending:
            index = pending.popleft()
            a, k, c = index // (width * width), index // width % width, index % width
            for aa in ((a, a + modulus) if a >= 8 else (a,)):
                for kk in ((k, k + modulus) if k >= 8 else (k,)):
                    for cc in ((c, c + modulus) if c >= 8 else (c,)):
                        result = nxt(aa, kk, cc)
                        if result is None:
                            continue
                        edges += 1
                        target = encode(*map(q, result))
                        if not seen[target]:
                            seen[target] = 1
                            pending.append(target)
        expected_edges = edges

    # Valid for any genuinely high halting family with j>=3,m>=2.
    # Right counter k satisfies k+j+3m+5 == 2^(2m+2)*(j+3).
    # For m>=2 the right side is divisible by the modulus (16 or 32).
    absent = {
        (jr, mr)
        for jr in range(modulus)
        for mr in range(modulus)
        if not seen[encode(q(2 * (jr + modulus) + 3),
                           q(5 * modulus - (jr + 3 * mr + 5)), q(0))]
    }
    return sum(seen), expected_edges, absent


def main() -> None:
    states16, edges16, absent16 = quotient(16)
    states32, edges32, absent32 = quotient(32)

    old24 = {
        (0, 13), (0, 25), (1, 28), (4, 25), (4, 29), (5, 16),
        (8, 1), (8, 5), (9, 4), (12, 5), (12, 17), (13, 24),
        (16, 9), (16, 29), (17, 12), (20, 9), (20, 13), (21, 0),
        (24, 17), (24, 21), (25, 20), (28, 1), (28, 21), (29, 8),
    }
    lifted16 = {(j, m) for j in range(32) for m in range(32)
                if (j % 16, m % 16) in absent16}
    new60 = absent32 - lifted16
    new36 = new60 - old24
    expected36 = {
        (0, 23), (1, 1), (1, 26), (2, 24), (3, 28), (4, 11),
        (5, 30), (6, 20), (7, 0), (8, 31), (9, 2), (9, 25),
        (10, 16), (11, 4), (12, 19), (13, 6), (14, 12), (15, 8),
        (16, 7), (17, 10), (17, 17), (18, 8), (19, 12), (20, 27),
        (21, 14), (22, 4), (23, 16), (24, 15), (25, 9),
        (25, 18), (26, 0), (27, 20), (28, 3), (29, 22),
        (30, 28), (31, 24),
    }
    assert (states16, edges16, len(absent16)) == (7115, 34992, 108)
    assert (states32, edges32, len(absent32)) == (31570, 189834, 492)
    assert len(lifted16) == 432
    assert len(new60) == 60
    assert len(old24) == 24 and old24 <= new60
    assert new36 == expected36 and len(new36) == 36

    print(f"B8/M16: states={states16}, edges={edges16}, excluded_pairs={len(absent16)}")
    print(f"B8/M32: states={states32}, edges={edges32}, excluded_pairs={len(absent32)}")
    print(f"M16→M32: lifted={len(lifted16)}, incremental={len(new60)}")
    print(f"M32 incremental: previously explicit={len(old24)}, extra={len(new36)}")
    for jr, mr in sorted(new36):
        print(f"{jr}\t{mr}")


if __name__ == "__main__":
    main()
