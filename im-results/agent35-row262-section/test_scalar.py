"""SFT: exact dyadic scalar A-section model for a rooted six-state Busy Beaver holdout.

This file is reproducible finite falsification evidence. The mathematical all-tape
argument is in Scalar.md; a finite test never decides the blank-tape halting question.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction
from random import Random

from test_row262 import RLE, macro


def dyadic_coordinate(ones: set[int], head: int) -> Fraction:
    """Coordinate P = sum 2^(head-cell) for finite-support physical tape."""
    return sum((Fraction(2) ** (head - cell) for cell in ones), Fraction(0))


def scalar_A(x: Fraction) -> tuple[Fraction | None, int, str]:
    """All-configuration exact A-section arithmetic; None means two-step F1 halt."""
    assert x >= 0 and x.denominator & (x.denominator - 1) == 0
    n = x.numerator // x.denominator
    frac = x - n
    if n % 2:
        v = n + 1
        e = 0
        while v % 2 == 0:
            v //= 2
            e += 1
        return (x + 1) / (2 ** (e + 1)), e + 3, "A1-E-sweep"
    if frac < Fraction(1, 2):
        return x + Fraction(3, 2), 2, "A0-B0"
    if frac >= Fraction(3, 4):
        return None, 2, "A0-F1-halt"
    b4 = int(16 * frac) % 2
    if b4 == 0:
        return 32 * (x + 1), 5, "A0-D0"
    b3 = int(8 * frac) % 2
    if b3 == 0:
        return 4 * x + Fraction(17, 4), 6, "A0-D1-C0"
    return 2 * x + Fraction(17, 8), 7, "A0-D1-C1"


def check_synthetic() -> None:
    rng = Random(0xBB620263)
    count = Counter()
    for i in range(10000):
        ones = {j for j in range(-16, 17) if rng.randrange(2)}
        head = rng.randrange(-8, 9)
        source = dyadic_coordinate(ones, head)
        predicted, predicted_duration, predicted_label = scalar_A(source)
        target_ones = set(ones)
        state, target_head, duration, label = macro("A", head, target_ones)
        assert (predicted_duration, predicted_label) == (duration, label), (i, source, label)
        if state == "F":
            assert predicted is None and duration == 2
        else:
            assert state == "A" and predicted == dyadic_coordinate(target_ones, target_head), (
                i, source, predicted, dyadic_coordinate(target_ones, target_head))
        count[label] += 1
    print("[synthetic] 10000 exact physical-tape/scalar identities:", dict(sorted(count.items())))


def check_blank() -> None:
    x = Fraction(0)
    head = 0
    tape: set[int] = set()
    time = 0
    n = 0
    counts = Counter()
    initial = [x]
    while True:
        y, duration, label = scalar_A(x)
        if time + duration > 200000:
            break
        assert y is not None, "Predicted a finite blank-origin halt"
        next_tape = set(tape)
        state, next_head, raw_duration, raw_label = macro("A", head, next_tape)
        assert state == "A" and (duration, label) == (raw_duration, raw_label)
        assert y == dyadic_coordinate(next_tape, next_head), (time, x, y)
        x = y
        head, tape = next_head, next_tape
        time += duration
        counts[label] += 1
        n += 1
        if len(initial) < 8:
            initial.append(x)
    assert time == 199996 and n == 42388, (time, n)
    print("[blank] first scalar iterates:", [str(x) for x in initial])
    print("[blank] A returns:", n, "primitive steps:", time)
    print("[blank] current scalar numerator/denominator bits:",
          x.numerator.bit_length(), x.denominator.bit_length())
    print("[blank] branch counts:", dict(sorted(counts.items())))
    print("[blank] next exact halting gate remains unresolved")


if __name__ == "__main__":
    print("[source]", RLE)
    check_synthetic()
    check_blank()
    print("PASS: finite test; no global blank-halt conclusion")
