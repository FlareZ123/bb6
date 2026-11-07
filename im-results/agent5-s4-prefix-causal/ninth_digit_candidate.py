"""Finite prefix-projection experiment for the ninth S4 stack digit.

This computes the first nine digits of the prefix map. It is not a full-root
survival proof; root transport to the prefix map is supplied by the Lean
prun_prefix theorem. The exact eight-digit cycle is proved in
S4PrefixEighthCycle.lean.
"""
from pathlib import Path
import sys

sys.path.insert(
    0,
    str(Path(__file__).resolve().parents[1] / "agent5-s4-all-depth-sharp"),
)
from checker import chain

OFFSETS = (509, 290, 219)
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


def prefix_run(steps: int, digits: tuple[int, ...]) -> tuple[int, ...]:
    state = digits
    for _ in range(steps):
        next_state = chain(OFFSETS, state)
        if next_state is None:
            raise AssertionError("projected prefix map halted")
        state = next_state
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
