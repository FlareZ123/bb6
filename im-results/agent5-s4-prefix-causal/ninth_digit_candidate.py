"""Finite prefix-projection experiment for the ninth S4 stack digit.

The projected hp/gp maps preserve the supplied prefix length. The full-root
checker uses a different empty-tail completion, so it must not be applied to a
truncated prefix.
"""
INITIAL_NINE = (
    283, 906, 982, 3490, 3734, 5935, 13580, 25036, 64260
)
EXPECTED_EIGHTH = (
    25036, 109210, 109208, 109209, 109206,
    109210, 109208, 109209, 109206,
    109210, 109208, 109209, 109206,
    109210, 109208, 109209, 109206, 109210,
)
EXPECTED_NINTH = (
    64260, 171050, 117512, 165780, 56245,
    171052, 117515, 165778, 56244,
    171051, 117511, 165779, 56247,
    171049, 117513, 165781, 56243, 171050,
)


def hp(head: int, tail: tuple[int, ...]) -> tuple[int, ...]:
    if not tail:
        return (head // 2 + 2,) if head % 2 == 0 else (head // 2,)
    digit, *rest = tail
    if head % 2 == 0:
        return (head // 2 + 2, digit + head // 2, *rest)
    return (head // 2, *hp(digit + head // 2 + 1, tuple(rest)))


def gp(offset: int, digits: tuple[int, ...]) -> tuple[int, ...]:
    if not digits:
        return ()
    return hp(digits[0] + offset, digits[1:])


def pp(digits: tuple[int, ...]) -> tuple[int, ...]:
    return gp(219, gp(290, gp(509, digits)))


def prefix_run(steps: int, digits: tuple[int, ...]) -> tuple[int, ...]:
    state = digits
    for _ in range(steps):
        state = pp(state)
    return state


def main() -> None:
    states = [INITIAL_NINE]
    for _ in range(17):
        states.append(prefix_run(5120, states[-1]))

    eighth = tuple(state[-2] for state in states)
    ninth = tuple(state[-1] for state in states)
    assert eighth == EXPECTED_EIGHTH, (eighth, EXPECTED_EIGHTH)
    assert ninth == EXPECTED_NINTH, (ninth, EXPECTED_NINTH)

    macro_cycle = tuple(ninth[k] for k in (1, 5, 9, 13, 17))
    assert macro_cycle == (171050, 171052, 171051, 171049, 171050)

    print("5120-return block boundaries (eighth, ninth):")
    for k, state in enumerate(states):
        print(f"{k:2d}: {state[-2]:>6d} {state[-1]:>7d}")
    print("candidate ninth-digit 20480-return cycle:", macro_cycle)


if __name__ == "__main__":
    main()
