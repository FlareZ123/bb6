"""Independent raw two-symbol D-start Turing machine check of a symbolic family.

This bounded regression cannot prove the quantified result in README.md.
Transition table is the literal 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---.
"""
from __future__ import annotations

TABLE: dict[tuple[int, int], tuple[int, int, int]] = {
    (0, 0): (1, 1, 1), (0, 1): (0, 1, 4),
    (1, 0): (1, -1, 2), (1, 1): (0, 1, 0),
    (2, 0): (1, -1, 0), (2, 1): (1, -1, 3),
    (3, 0): (1, -1, 2), (3, 1): (1, -1, 5),
    (4, 0): (0, -1, 2), (4, 1): (0, -1, 1),
    (5, 0): (1, -1, 4),
}


def physical_return(right: list[int], max_steps: int = 400000) -> tuple[int, list[int]]:
    occupied: set[int] = {i for i, bit in enumerate(right, start=1) if bit}
    head, state = 0, 5
    for elapsed in range(1, max_steps + 1):
        transition = TABLE.get((state, int(head in occupied)))
        if transition is None:
            raise AssertionError(f"halted before return at {elapsed - 1} transitions")
        write, shift, state = transition
        if write:
            occupied.add(head)
        else:
            occupied.discard(head)
        head += shift
        if state == 5 and head not in occupied and all(i > head for i in occupied):
            return elapsed, [int(i in occupied) for i in range(head + 1, max(occupied, default=head) + 1)]
    raise AssertionError(f"no physical F/0 return in {max_steps} steps")


def one(n: int) -> list[int]:
    return [1] * n


def pairs(n: int) -> list[int]:
    return [0, 1] * n


def model(t: int, q: int) -> tuple[tuple[int, list[int]], tuple[int, list[int]]]:
    assert q >= 3
    k, K = 3 * t + 1, 8 * t + 3
    first = (
        12 * k * k + 49 * k + 56 + 4 * q,
        one(8 * k + 5) + [0] + one(2 * q) + [0] + one(6),
    )
    second = (
        12 * K * K + 49 * K + 58,
        one(8 * K + 9) + pairs(2) + [0] + one(2 * q - 3) + [0] + one(6),
    )
    return first, second


def main() -> None:
    tested = 0
    for t in range(5):
        for q in range(3, 12):
            k = 3 * t + 1
            start = one(3 * k + 4) + pairs(q) + one(1)
            first_time, first_right = physical_return(start)
            second_time, second_right = physical_return(first_right)
            first, second = model(t, q)
            assert first_time == first[0] and first_right == first[1], (t, q, "first")
            assert second_time == second[0] and second_right == second[1], (t, q, "second")
            tested += 1
    print(f"PASS {tested} independent exact two-return checks (t=0..4, q=3..11)")
    print("Smallest witness: k=1, q=3, first time=129, second time=313, total=442")


if __name__ == "__main__":
    main()
