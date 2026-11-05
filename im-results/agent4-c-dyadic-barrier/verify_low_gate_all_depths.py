"""Independent exact Machine C low-family predecessor-degree verification.

Enumerates *all* source candidates from the original full section inverse
grammar, then independently computes 2-adic formula parents and checks both
lists against the literal original bounce/section transition functions.

This is finite numerical corroboration of LowAllMInDegree.md, whose paper
proof depends on the previously original-source Lean-verified inverse iff.
"""

def v2(x: int) -> int:
    assert x > 0
    return (x & -x).bit_length() - 1


def bounce(k: int, c: int) -> tuple[int, int] | None:
    while c >= 4:
        if k % 2:
            if c <= 2 * k + 6:
                return 2 * k + 6 - c, c
            b = 2 * k + 3
            k, c = b, c - b
        else:
            if c == 4:
                return 2 * k + 2, 3
            if c == 5:
                return None
            if c <= 2 * k + 8:
                return 2 * k + 8 - c, c - 1
            b = 2 * k + 5
            k, c = 2 * k + 4, c - b
    return None


def sec_next(a: int, k: int) -> tuple[int, int] | None:
    if a == 0:
        if k == 0:
            return None
        if k == 1:
            return 0, 4
        return bounce(1, 2 * k + 1)
    if a == 1:
        if k == 0:
            return 5, 1
        if k == 1:
            return 2, 3
        if k == 2:
            return 2, 5
        if k == 3:
            return 0, 7
        return bounce(4, 2 * k - 3)
    if k == 0:
        return a - 2, 2
    if 2 * k <= a:
        return a - 2 * k, 2 * k + 2
    return bounce(a - 1, 2 * k - a + 3)


def all_parents_from_grammar(m: int) -> list[tuple[int, int]]:
    """Exhaust the complete source inverse *equations*, independently."""
    D = 2 ** (2 * m + 3)
    K = D - 3 * m - 4
    S, T = K + 1, K + 2
    parents: list[tuple[int, int]] = []
    for n in range(T.bit_length() + 1):
        # Exceptional source a=0, high odd-bounce output.
        if 8 * (1 << n) == S and (2 * K - 8 - 3 * n) % 2 == 0:
            k = (2 * K - 8 - 3 * n) // 2
            if k >= 2 and sec_next(0, k) == (1, K):
                parents.append((0, k))
        # Exceptional source a=1, high even-bounce output.
        if 16 * (1 << n) == T and (2 * K - 10 - 3 * n) % 2 == 0:
            k = (2 * K - 10 - 3 * n) // 2
            if k >= 4 and sec_next(1, k) == (1, K):
                parents.append((1, k))
        # Any even-first high odd-bounce source.
        if S % (1 << (n + 1)) == 0:
            a = S // (1 << (n + 1)) - 2
            twice_k = 2 * K - a - 6 - 3 * n
            if a >= 2 and a % 2 == 0 and twice_k >= 2 and twice_k % 2 == 0:
                k = twice_k // 2
                if a < 2 * k and sec_next(a, k) == (1, K):
                    parents.append((a, k))
        # Any odd-first high even-bounce source.
        if T % (1 << (n + 1)) == 0:
            a = T // (1 << (n + 1)) - 3
            twice_k = 2 * K - a - 6 - 3 * n
            if a >= 3 and a % 2 == 1 and twice_k >= 2 and twice_k % 2 == 0:
                k = twice_k // 2
                if a < 2 * k and sec_next(a, k) == (1, K):
                    parents.append((a, k))
    if K >= 4 and K % 2 == 0:
        direct = K - 1, (K - 2) // 2
        assert sec_next(*direct) == (1, K)
        parents.append(direct)
    assert len(parents) == len(set(parents))
    return sorted(parents)


def formula_parents(m: int) -> list[tuple[int, int]]:
    D = 2 ** (2 * m + 3)
    K = D - 3 * m - 4
    parents: list[tuple[int, int]] = []
    if m % 2:
        S = K + 1
        for r in range(v2(m + 1) // 2):
            assert S % (2 ** (2 * r + 1)) == 0
            a = S // 2 ** (2 * r + 1) - 2
            twice_k = 2 * K - a - 6 * r - 6
            assert twice_k % 2 == 0
            k = twice_k // 2
            assert a >= 2 and a % 2 == 0 and k > 0 and a < 2 * k
            assert sec_next(a, k) == (1, K)
            parents.append((a, k))
    else:
        parents.append((K - 1, (K - 2) // 2))
        for r in range((v2(3 * m + 2) - 1) // 2):
            T = K + 2
            assert T % (2 ** (2 * r + 2)) == 0
            a = T // 2 ** (2 * r + 2) - 3
            twice_k = 2 * K - a - 6 * r - 9
            assert twice_k % 2 == 0
            k = twice_k // 2
            assert a >= 3 and a % 2 == 1 and k > 0 and a < 2 * k
            assert sec_next(a, k) == (1, K)
            parents.append((a, k))
    assert len(parents) == len(set(parents))
    return sorted(parents)


def main() -> None:
    for m in range(501):
        grammar = all_parents_from_grammar(m)
        formula = formula_parents(m)
        assert grammar == formula, (m, grammar, formula)
    for m in (1000, 10000, 100000, 1023, 4095, 9999):
        formula_parents(m)
    print("PASS: 501 complete inverse-grammar enumerations")
    print("PASS: 6 large-depth original bounce witness sets")
    print("PASS: all degrees and every enumerated source coincide with the 2-adic formula")


if __name__ == "__main__":
    main()
