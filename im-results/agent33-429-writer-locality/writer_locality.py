"""Exact six-state #429 finite local-counterexample certificates.

Machine: 1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA.
This finite regression is no blank-tape halt/nonhalt proof.
"""
from __future__ import annotations

TABLE = {
    (0, 0): (1, 1, 1), (0, 1): (0, -1, 5),
    (1, 0): (1, 1, 2), (1, 1): (1, 1, 0),
    (2, 0): (0, 1, 3), (2, 1): (0, 1, 1),
    (3, 0): (1, -1, 4),
    (4, 0): (0, -1, 0), (4, 1): (1, -1, 4),
    (5, 0): (1, 1, 3), (5, 1): (1, -1, 0),
}


def step(cfg: tuple[int, int, set[int]]) -> tuple[int, int, set[int]]:
    state, head, ones = cfg
    write, direction, new_state = TABLE[(state, int(head in ones))]
    new_ones = ones.copy()
    if write:
        new_ones.add(head)
    else:
        new_ones.discard(head)
    return new_state, head + direction, new_ones


def leftbits(cfg: tuple[int, int, set[int]], count: int) -> tuple[int, ...]:
    _, head, ones = cfg
    return tuple(int(head - j in ones) for j in range(1, count + 1))


def seeded_writer(cfg: tuple[int, int, set[int]]) -> tuple[int, int, set[int]]:
    state, _, _ = cfg
    near = leftbits(cfg, 8)
    return state, 0, ({0} if state == 5 else set()) | {
        -j for j, bit in enumerate(near, 1) if bit
    }


def compare_at(
    n: int, required_state: int, expected_byte: int,
    fatal_delay: int, divergence_delay: int,
) -> None:
    cfg = (0, 0, set())
    for _ in range(n):
        cfg = step(cfg)
    state, head, ones = cfg
    assert state == required_state
    assert (head in ones) == (state == 5)
    near = leftbits(cfg, 8)
    assert sum(bit << j for j, bit in enumerate(near)) == expected_byte
    assert head + 1 not in ones

    synthetic = seeded_writer(cfg)
    actual = (state, 0, {p - head for p in ones})
    first_diff = None
    max_synthetic_head = 0
    for k in range(fatal_delay + 1):
        if first_diff is None and actual != synthetic:
            if (actual[0], actual[1], actual[1] in actual[2]) != (
                    synthetic[0], synthetic[1], synthetic[1] in synthetic[2]):
                first_diff = (
                    k, actual[1], int(actual[1] in actual[2]),
                    int(synthetic[1] in synthetic[2]),
                )
        if k == fatal_delay:
            assert synthetic[0] == 2 and synthetic[1] == -1
            assert -1 not in synthetic[2] and 0 in synthetic[2]
            break
        actual = step(actual)
        synthetic = step(synthetic)
        max_synthetic_head = max(max_synthetic_head, synthetic[1])

    assert first_diff == (divergence_delay, -9, 1, 0), first_diff
    assert max_synthetic_head == 0
    print(
        f"ROOT_WRITER={n} state={required_state} head={head}"
        f" left8=0x{expected_byte:02x}"
    )
    print(
        f"SYNTHETIC_FATAL_C01={fatal_delay}"
        f" first_differing_read={first_diff} max_head={max_synthetic_head}"
    )


if __name__ == "__main__":
    compare_at(276, 3, 0xFE, 27, 9)
    compare_at(283, 5, 0x57, 59, 13)
    print("PASS: two exact finite root-neighborhood/synthetic comparisons")
