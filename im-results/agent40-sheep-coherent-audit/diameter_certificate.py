"""Independent finite regression of the all-p generic Sheep dyadic diameter proof.

The source inverse map and canonical decoder are separately reconstructed here.
For every maximal-code source modulo 2^p, test every even terminal residue.
Finite testing corroborates the all-parameter proof in DYADIC-DIAMETER.md.
"""
from math import comb


def v2(n: int) -> int:
    assert n > 0
    return (n & -n).bit_length() - 1


def decode(p: int, source: int) -> list[tuple[int, int]]:
    """Canonical inverse word for an even residue mod 2^p."""
    word = []
    assert p >= 1 and source % 2 == 0 and 0 <= source < 2**p
    while source:
        a = v2(source)
        u = source >> a
        C = (1 + 2**(a+1))*u + 2*a - 3
        h = min(v2(C) - 1, p - a - 1)
        assert a >= 1 and h >= 0
        word.append((a, h))
        p -= a+h+1
        source = (1 + 3**h*(C >> (h+1))) % (2**p)
        assert source % 2 == 0
    return word


def inverse(p: int, a: int, h: int, target: int) -> int:
    """Exact modular inverse letter T[p,a,h](target), with odd inverses."""
    assert 1 <= a < p and 0 <= h < p-a and target % 2 == 0
    m = 2**(p-a)
    d = 1 + 2**(a+1)
    u = ((3-2*a+2**(h+1)*pow(3**h, -1, m)*(target-1))
         * pow(d, -1, m)) % m
    return 2**a*u


def apply_word(p: int, word: list[tuple[int, int]], terminal: int) -> int:
    source = terminal
    for a, h in reversed(word):
        source = inverse(p, a, h, source)
    return source


def run() -> None:
    total_sources = 0
    total_pairs = 0
    for p in range(1, 16):
        k = p//2
        maximal = []
        for source in range(0, 2**p, 2):
            word = decode(p, source)
            assert len(word) <= k and sum(a+h+1 for a,h in word) <= p
            if len(word) == k:
                maximal.append((source, word))
        assert len(maximal) == comb(p, 2*k)
        for source, word in maximal:
            cost = sum(a+h+1 for a,h in word)
            assert cost >= p-1
            assert apply_word(p, word, 0) == source
            for terminal in range(0, 2**p, 2):
                assert apply_word(p, word, terminal) == source, (
                    p, source, terminal, word
                )
                total_pairs += 1
            total_sources += 1
        print(
            f"PASS p={p}: maximal-code sources={len(maximal)}, "
            f"all {2**(p-1)} even targets per source",
            flush=True,
        )
    print(
        f"PASS {total_sources} maximal-code sources and "
        f"{total_pairs} source/target pairs through p=15",
        flush=True,
    )


if __name__ == "__main__":
    run()
