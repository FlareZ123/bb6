"""Construct D-start Cryptid halting extensions for every unary F-on-zero input.

A formal existence proof is in UniversalExtension.lean:
  BB6.CryptidUniversalExtension.every_unary_has_halting_extension_all
Source-authenticated Lean 4.36.0-rc2 CI: GitHub Actions run 41489869859.

The generator uses the same explicit certified B-return and A/E halting
formulas. The reference simulator independently executes the original
six-state two-symbol raw transition table, with an attempted halt counted
as one step. All tapes are zero outside their finite recorded supports.

Neither this file nor the theorem asserts that an extension is visited
from the original BLANK starting configuration.
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class HaltingWitness:
    unary_length: int
    suffix_bits: str
    halt_step: int
    b_returns: int
    terminal_unary_length: int


def halting_extension(n: int) -> HaltingWitness:
    """Choose a finite right suffix with a provable exact halting time at I_n."""
    if n < 0:
        raise ValueError("Unary length must be nonnegative")
    if n == 0:
        return HaltingWitness(0, "0001101100", 151, 0, 0)
    if n == 1:
        return HaltingWitness(1, "01101100", 74, 0, 1)

    b_returns = 0
    steps = 0
    terminal = n
    while terminal % 3 == 2:
        k = (terminal - 2) // 3
        steps += 12 * k * k + 49 * k + 40
        terminal = 8 * k + 9
        b_returns += 1

    if terminal % 3 == 0:
        k = (terminal - 3) // 3
        suffix = "0" * b_returns + "01101101100"
        steps += 12 * k * k + 41 * k + 101
    else:
        k = (terminal - 4) // 3
        suffix = "0" * b_returns + "01101100"
        steps += 12 * k * k + 41 * k + 99
    return HaltingWitness(n, suffix, steps, b_returns, terminal)


def independent_raw_halt_step(n: int, suffix_bits: str, max_steps: int) -> int | None:
    """Run the unaccelerated raw six-state machine until its first halt."""
    tape = {i: 1 for i in range(1, n + 1)}
    tape.update({n + i + 1: 1 for i, bit in enumerate(suffix_bits) if bit == "1"})
    rules = (
        ((1, 1, 1), (0, 1, 4)),
        ((1, -1, 2), (0, 1, 0)),
        ((1, -1, 0), (1, -1, 3)),
        ((1, -1, 2), (1, -1, 5)),
        ((0, -1, 2), (0, -1, 1)),
        ((1, -1, 4), None),
    )
    position, state = 0, 5
    for step in range(1, max_steps + 1):
        rule = rules[state][tape.get(position, 0)]
        if rule is None:
            return step
        written, direction, next_state = rule
        if written:
            tape[position] = 1
        else:
            tape.pop(position, None)
        position += direction
        state = next_state
    return None


def check_small_witnesses(count: int = 25) -> list[HaltingWitness]:
    """Reproduce exact halting steps for the first count inputs by raw simulation."""
    checked = []
    for n in range(count):
        witness = halting_extension(n)
        actual = independent_raw_halt_step(n, witness.suffix_bits, witness.halt_step)
        assert actual == witness.halt_step, (n, witness, actual)
        checked.append(witness)
    return checked
