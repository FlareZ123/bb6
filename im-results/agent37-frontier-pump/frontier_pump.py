"""Exact source-table prefix-frontier experiments for Cryptid D.

A finite observation never reads the unknown right-tail marker. Consequently
its endpoint statement holds for every possible continuation of that tail.
The all-word four-pair pump conjecture tested here remains unproved.
"""
from dataclasses import dataclass
from itertools import product
from random import Random

# Six-state table: A=0, B=1, C=2, D=3, E=4, F=5.
WRITE = ((1, 0), (1, 0), (1, 1), (1, 1), (0, 0), (1, 0))
MOVE = ((1, 1), (-1, 1), (-1, -1), (-1, -1), (-1, -1), (-1, 0))
NEXT = ((1, 4), (2, 0), (0, 3), (2, 5), (2, 1), (4, -1))


@dataclass(frozen=True)
class Event:
    kind: str
    steps: int
    state: int = -1
    top: str = ""
    pairs: int = -1
    right: str = ""


def first_event(state: int, top: str, pairs: int, bit: int,
                limit: int = 200_000) -> Event:
    """Run from a chosen frontier bit with unknown cells at positions >=1.

    The nearest-first left tape equals top + (01)^pairs + 1; all other
    positions not explicitly specified start blank. The first event is an
    undefined F/1, a physically blank-left F/0, or a read at position 1.
    """
    left = top + "01" * pairs + "1"
    tape = {-(i + 1): 1 for i, ch in enumerate(left) if ch == "1"}
    if bit:
        tape[0] = 1
    head = 0
    left_ones = sum(tape.get(i, 0) for i in range(-len(left), 0))

    for steps in range(limit + 1):
        if head >= 1:
            nearest = min((i for i, v in tape.items() if i < head and v),
                          default=head)
            word = "".join(str(tape.get(i, 0))
                           for i in range(head - 1, nearest - 1, -1))
            count = -1
            for n in range((len(word) - 1) // 2 + 1):
                if word.endswith("01" * n + "1"):
                    count = n
            prefix = word[:len(word) - (2 * count + 1)] if count >= 0 else word
            return Event("frontier", steps, state, prefix, count)

        old_bit = tape.get(head, 0)
        successor = NEXT[state][old_bit]
        if successor == -1:
            return Event("halt", steps)
        written = WRITE[state][old_bit]
        if written:
            tape[head] = 1
        else:
            tape.pop(head, None)
        direction = MOVE[state][old_bit]
        if direction == 1:
            left_ones += written
            head += 1
        else:
            head -= 1
            left_ones -= tape.get(head, 0)
        state = successor

        if state == 5 and tape.get(head, 0) == 0 and left_ones == 0:
            right = "".join(str(tape.get(i, 0)) for i in range(head + 1, 1))
            return Event("return", steps + 1, right=right + "$")
    return Event("timeout", limit)


def compare(state: int, top: str, pairs: int, bit: int):
    first = first_event(state, top, pairs, bit)
    second = first_event(state, top, pairs + 4, bit)
    if first.kind != second.kind or first.kind == "timeout":
        return False, first, second
    if first.kind == "frontier":
        shape = (first.state == second.state and first.top == second.top
                 and second.pairs == first.pairs + 4)
    elif first.kind == "return":
        shape = second.right == "1" * 8 + first.right
    else:
        shape = True
    delta = second.steps - first.steps - (8 if first.kind == "return" else 0)
    return shape and delta >= 0 and delta % 24 == 0, first, second


def main():
    checks = 0
    for length in range(9):
        for bits in product("01", repeat=length):
            top = "".join(bits)
            for state in (0, 1, 4):
                for bit in (0, 1):
                    for pairs in range(3, 8):
                        ok, a, b = compare(state, top, pairs, bit)
                        assert ok, (top, state, bit, pairs, a, b)
                        checks += 1
    print("exhaustive_j_ge_3", checks, "passed")

    bad = (("10010", 1, 0), ("010010", 4, 1),
           ("110100", 1, 0), ("110100", 4, 0))
    for top, state, bit in bad:
        ok, a, b = compare(state, top, 2, bit)
        assert not ok, (top, state, bit)
        print("j2_counterexample", top, state, bit, a, b)

    rng = Random(37)
    for trial in range(20_000):
        top = "".join(str(rng.getrandbits(1)) for _ in range(rng.randrange(180)))
        state = rng.choice((0, 1, 4))
        bit = rng.getrandbits(1)
        pairs = rng.choice((3, 4, 5, 6, 8, 12))
        ok, a, b = compare(state, top, pairs, bit)
        assert ok, (trial, top, state, bit, pairs, a, b)
    print("random_j_ge_3", 20_000, "passed")


if __name__ == "__main__":
    main()
