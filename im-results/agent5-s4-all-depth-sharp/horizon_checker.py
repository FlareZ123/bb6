"""Finite-horizon S4 universal-suffix risk and one-digit witness.

The exact theorem is S4MultiSharp.all_suffix_iff_nGood. This implementation
follows source-defined G and P operations in checker.py. Its root-seed
example is synthetic and does not decide the original blank-tape machine.
"""
from dataclasses import dataclass
from typing import Sequence

from checker import chain, drain, weight

S4_OFFSETS = (509, 290, 219)
S4_SEED = (301, 650, 645, 322, 163, 160)


@dataclass(frozen=True, slots=True)
class HorizonVerdict:
    universally_safe: bool
    failure_return: int | None = None
    failure_drain: int | None = None
    witness_digit: int | None = None


def check_horizon(
    prefix: Sequence[int],
    returns: int,
    offsets: Sequence[int] = S4_OFFSETS,
) -> HorizonVerdict:
    """Exact Boolean universal-suffix criterion for a finite horizon.

    The witness digit, if present, makes the whole odd-drain return pipeline
    stop on or before failure_return + 1 starting from the original prefix.
    """
    k = len(prefix)
    modulus = 1 << k
    current = tuple(prefix)
    for return_number in range(returns):
        for drain_number, offset in enumerate(offsets):
            potential = weight(current) + offset
            if potential % modulus == 0:
                quotient = potential // modulus
                witness = (1 << quotient.bit_length()) - quotient - 1
                return HorizonVerdict(False, return_number, drain_number, witness)
            nxt = drain(offset, current)
            assert nxt is not None
            current = nxt
    return HorizonVerdict(True)


def run_returns(
    initial: Sequence[int],
    returns: int,
    offsets: Sequence[int] = S4_OFFSETS,
) -> tuple[int, ...] | None:
    current: tuple[int, ...] | None = tuple(initial)
    for _ in range(returns):
        current = chain(offsets, current)
        if current is None:
            return None
    return current


def reproduce() -> None:
    verdict = check_horizon(S4_SEED, 18)
    assert verdict == HorizonVerdict(False, 17, 2, 1043)
    assert run_returns((*S4_SEED, 1043), 18) is None
    unextended = run_returns(S4_SEED, 18)
    assert unextended is not None and len(unextended) == 10
    print("S4 seed, 18 returns:", verdict)
    print("Unextended seed survives with length", len(unextended))
    print("One-digit synthetic extension [1043] halts at return 18")


if __name__ == "__main__":
    reproduce()
