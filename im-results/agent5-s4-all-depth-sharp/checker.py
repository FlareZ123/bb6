"""Executable witness extractor for the verified S4 odd-drain prefix theorem.

Inputs are finite tuples of natural-number digits and positive offsets.
The all-suffix correctness theorem is in S4AllDepthSharp.lean.
"""
from dataclasses import dataclass
from typing import Sequence


@dataclass(frozen=True, slots=True)
class PrefixVerdict:
    universally_safe: bool
    failing_stage: int | None = None
    witness_digit: int | None = None
    terminal_power_exponent: int | None = None


def weight(digits: Sequence[int]) -> int:
    return sum((digit + 1) << i for i, digit in enumerate(digits))


def odd_drain(head: int, tail: Sequence[int]) -> tuple[int, ...] | None:
    emitted: list[int] = []
    for digit in tail:
        if head % 2 == 0:
            return (*emitted, head // 2 + 2, digit + head // 2, *tail[len(emitted) + 1:])
        emitted.append(head // 2)
        head = digit + head // 2 + 1
    while head % 2:
        if head <= 1:
            return None
        emitted.append(head // 2)
        head //= 2
    if head == 0:
        return None
    return (*emitted, head // 2 + 2, head // 2 - 1)


def drain(offset: int, digits: Sequence[int]) -> tuple[int, ...] | None:
    if not digits:
        return odd_drain(offset - 1, ())
    return odd_drain(digits[0] + offset, digits[1:])


def chain(offsets: Sequence[int], digits: Sequence[int]) -> tuple[int, ...] | None:
    value: tuple[int, ...] | None = tuple(digits)
    for offset in offsets:
        value = drain(offset, value)
        if value is None:
            return None
    return value


def classify_prefix(offsets: Sequence[int], prefix: Sequence[int]) -> PrefixVerdict:
    """Classify all suffixes; if unsafe, supply an exact one-digit halter."""
    k = len(prefix)
    modulus = 1 << k
    value = tuple(prefix)
    for stage, offset in enumerate(offsets):
        potential = weight(value) + offset
        if potential % modulus == 0:
            quotient = potential // modulus
            exponent = quotient.bit_length()
            digit = (1 << exponent) - quotient - 1
            return PrefixVerdict(False, stage, digit, k + exponent)
        next_value = drain(offset, value)
        assert next_value is not None  # Guaranteed by the source power gate.
        value = next_value
    return PrefixVerdict(True)
