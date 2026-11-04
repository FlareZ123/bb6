"""Independent sparse physical-tape check of three exceptional E/A families.

Each sample begins on a genuine F/0 configuration with physically blank left
tape and unary length 9*t+10 followed by (01)^q 1. The simulator uses the
literal eleven live transitions of six-state Machine D, including its F/1
undefined halt. Both returned configurations must be the FIRST two physical
F/0 sections. Full physical tape content and exact time are compared.

This is finite regression evidence. The corresponding all-parameter proof
modules EAResidueTwoSource.lean and EAResidueOneSource.lean require Lean CI.
"""

from time import perf_counter

TRANSITIONS = (
    ((1, 1, 1), (0, 1, 4)),
    ((1, -1, 2), (0, 1, 0)),
    ((1, -1, 0), (1, -1, 3)),
    ((1, -1, 2), (1, -1, 5)),
    ((0, -1, 2), (0, -1, 1)),
    ((1, -1, 4), None),
)


def a_token_cost(m: int, word: list[int]) -> tuple[int, int]:
    cost = 0
    for token in word:
        if token:
            cost += 6 * m + 41
            m += 4
        else:
            cost += 2
            m += 1
    return cost, m


def predicted(t: int, q: int) -> tuple[int, int, int, list[int]]:
    e = 3 * t + 2
    a = 8 * t + 6
    first = 12 * e * e + 49 * e + 64 + 4 * (q - 2)
    if q % 3 == 0:
        v = q // 3
        word = [1] * (2 * v)
        final = 64 * t + 65 + 16 * v
        suffix: list[int] = []
        close = 6
    elif q % 3 == 2:
        v = q // 3
        word = [1] * (2 * v + 1) + [0, 1, 1]
        final = 64 * t + 85 + 16 * v
        suffix = []
        close = 6
    else:
        v = q // 3
        word = [1] * (2 * v)
        final = 64 * t + 59 + 16 * v
        suffix = [0, 1, 0, 1, 0, 1, 1, 1]
        close = 24
    token_cost, final_m = a_token_cost(4 * a + 3, word)
    second = first + 12 * a * a + 41 * a + 32 + token_cost + 2 * final_m + close
    return first, second, final, suffix


def verify(t: int, q: int) -> None:
    length = 9 * t + 10
    ones = set(range(1, length + 1))
    for i in range(q):
        ones.add(length + 2 + 2 * i)
    ones.add(length + 1 + 2 * q)

    head = 0
    state = 5
    first, second, final, suffix = predicted(t, q)
    first_length = 8 * (3 * t + 2) + 5
    first_suffix = [0] + [1] * (2 * q) + [0] + [1] * 6

    for time in range(1, second + 1):
        transition = TRANSITIONS[state][head in ones]
        if transition is None:
            raise AssertionError((t, q, "unexpected halt", time))
        value, direction, state = transition
        if value:
            ones.add(head)
        else:
            ones.discard(head)
        head += direction

        physical_return = (
            state == 5
            and head not in ones
            and all(x >= head for x in ones)
        )
        if physical_return and time not in (first, second):
            raise AssertionError((t, q, "unexpected earlier return", time))
        if time in (first, second):
            if not physical_return:
                raise AssertionError((t, q, "missing physical return", time))
            n = first_length if time == first else final
            tail = first_suffix if time == first else suffix
            expected = set(range(head + 1, head + n + 1))
            expected.update(
                head + n + 1 + i for i, b in enumerate(tail) if b
            )
            if ones != expected:
                raise AssertionError(
                    (t, q, "wrong tape", time, len(ones), len(expected))
                )


def main() -> None:
    begun = perf_counter()
    samples = 0
    primitive_steps = 0
    for t in range(7):
        for q in range(2, 31):
            verify(t, q)
            primitive_steps += predicted(t, q)[1]
            samples += 1
    print(
        f"PASS: {samples} two-return full physical-tape cases, "
        f"{primitive_steps:,} primitive steps, "
        f"{perf_counter() - begun:.2f} seconds"
    )


if __name__ == "__main__":
    main()
