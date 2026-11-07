"""Counterexample to generic monotonicity of S4 odd gate quotients.

Finite source-shaped simulation, on a SYNTHETIC six-digit stack in the
same four-head cyclic sector as the true reduced root. Does not decide BB(6).
"""
from checker import chain, weight


def odd_part(value: int) -> int:
    while value % 2 == 0:
        value //= 2
    return value


def reproduce() -> None:
    initial = (280, 1903, 4054, 46, 1286, 3315)
    current = initial
    exposures: list[tuple[int, int, int, int]] = []
    for n in range(211):
        value = current
        for j, c in enumerate((509, 290, 219)):
            p = weight(value) + c
            if p % (1 << len(current)) == 0:
                q = p >> len(current)
                exposures.append((n, j, q, odd_part(q)))
            nxt = chain((c,), value)
            assert nxt is not None
            value = nxt
        current = value

    assert exposures == [
        (18, 2, 7209, 7209),
        (68, 0, 14307, 14307),
        (210, 2, 27118, 13559),
    ]
    print("Synthetic S4 odd-part monotonicity fails:", exposures)
    print("14307 > 13559 at consecutive exposure times 68, 210")


if __name__ == "__main__":
    reproduce()
