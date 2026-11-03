"""Finite raw-vs-section regression for Oct16 BB6 rooted line 262.

This is observational testing, not a halting/nonhalting proof.
Uses only the Python standard library; run directly as a single test file.
"""
from __future__ import annotations

from collections import Counter
from hashlib import sha256
from fractions import Fraction
from random import Random

RLE = "1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA0LE_0RC---"
TABLE = {}
for state, block in zip("ABCDEF", RLE.split("_"), strict=True):
    assert len(block) == 6
    for bit in range(2):
        a = block[3 * bit:3 * bit + 3]
        if a != "---":
            TABLE[state, bit] = (int(a[0]), 1 if a[1] == "R" else -1, a[2])
assert len(TABLE) == 11


def raw(state: str, pos: int, tape: set[int]) -> tuple[str, int]:
    write, direction, next_state = TABLE[state, pos in tape]
    if write:
        tape.add(pos)
    else:
        tape.discard(pos)
    return next_state, pos + direction


def macro(state: str, pos: int, tape: set[int]) -> tuple[str, int, int, str]:
    """One complete A-to-A or A-to-frozen-halt section."""
    assert state == "A"
    if pos in tape:
        tape.remove(pos)
        k, x = 0, pos - 1
        while x in tape:
            tape.remove(x)
            x -= 1
            k += 1
        tape.add(x)
        return "A", x - 1, k + 4, "A1-E-sweep"
    tape.add(pos)
    if pos + 1 not in tape:
        tape.add(pos + 1)
        return "A", pos, 2, "A0-B0"
    if pos + 2 in tape:
        return "F", pos + 2, 2, "A0-F1-halt"
    if pos + 4 not in tape:
        return "A", pos + 5, 5, "A0-D0"
    tape.remove(pos + 4)
    if pos + 3 not in tape:
        tape.add(pos + 3)
        return "A", pos + 2, 6, "A0-D1-C0"
    tape.remove(pos + 3)
    tape.add(pos + 2)
    return "A", pos + 1, 7, "A0-D1-C1"


def digest(state: str, pos: int, tape: set[int]) -> str:
    return sha256((f"{state}|{pos}|" +
                   ",".join(map(str, sorted(tape)))).encode("ascii")).hexdigest()



COEFFICIENT = {
    "A1-E-sweep": Fraction(1),
    "A0-B0": Fraction(3, 2),
    "A0-F1-halt": Fraction(1),
    "A0-D0": Fraction(1),
    "A0-D1-C0": Fraction(17, 16),
    "A0-D1-C1": Fraction(17, 16),
}


def energy(tape: set[int]) -> Fraction:
    """Positive dyadic tape potential in fixed integer coordinates."""
    return sum((Fraction(2) ** (-pos) for pos in tape), Fraction(0))


def check_synthetic() -> None:
    rng = Random(0xBB620262)
    tally = Counter()
    for trial in range(10000):
        tape = {p for p in range(-16, 17) if rng.randrange(2)}
        position = rng.randrange(-8, 9)
        accelerated = set(tape)
        s, p, duration, label = macro("A", position, accelerated)
        actual = set(tape)
        state, head = "A", position
        for step_no in range(1, duration + 1):
            state, head = raw(state, head, actual)
            if step_no < duration:
                assert (state, head in actual) in TABLE
                assert state != "A"
        assert (s, p, accelerated) == (state, head, actual), (trial, label)
        assert energy(accelerated) - energy(tape) == COEFFICIENT[label] * (Fraction(2) ** (-position)), (trial, label)
        tally[label] += 1
    print("[synthetic] 10000 exact matches:", dict(sorted(tally.items())))


def check_blank() -> None:
    state, pos, tape = "A", 0, set()
    steps = 0
    tally = Counter()
    checkpoints = {}
    while steps < 200000:
        shadow = set(tape)
        s, p, duration, label = macro(state, pos, shadow)
        if steps + duration > 200000:
            break
        for _ in range(duration):
            state, pos = raw(state, pos, tape)
        steps += duration
        assert (state, pos, tape) == (s, p, shadow), (steps, label)
        assert (state, pos in tape) in TABLE, "Halted in prefix"
        tally[label] += 1
        if steps in (6, 26, 86, 122):
            checkpoints[steps] = digest(state, pos, tape)
    # Second independent unaccelerated execution and synchronized raw checkpoint.
    s, p, t = "A", 0, set()
    for n in range(1, 200001):
        s, p = raw(s, p, t)
        assert (s, p in t) in TABLE, ("Halted in raw prefix", n)
        if n == steps:
            assert (s, p, t) == (state, pos, tape)
    print("[blank] raw steps 200000; macro-aligned:", steps)
    print("[blank] section counts:", dict(sorted(tally.items())))
    print("[blank] raw final: state", s, "head", p, "ones", len(t),
          "sha256", digest(s, p, t))
    print("[blank] section digests:", checkpoints)
    assert steps == 199996
    assert sum(tally.values()) == 42388
    assert tally["A0-F1-halt"] == 0


if __name__ == "__main__":
    print("[source]", RLE, "transition-count:", len(TABLE))
    check_synthetic()
    check_blank()
    print("PASS: finite observations only; no BB(6) value inferred")
