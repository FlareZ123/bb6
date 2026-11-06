"""Independent physical zipper-tape regression for cylinder_first_event.py.

This implementation uses separate left/right deques instead of a sparse set
and recomputes the physical-blank predicate from the entire left tape.
"""
from collections import deque
import random
from cylinder_first_event import certify, evaluate, check

RULES = (
    ((1, 1, 1), (0, 1, 4)),
    ((1, -1, 2), (0, 1, 0)),
    ((1, -1, 0), (1, -1, 3)),
    ((1, -1, 2), (1, -1, 5)),
    ((0, -1, 2), (0, -1, 1)),
    ((1, -1, 4), None),
)


def raw_first_event(phase: int, m: int, word: str, cap: int = 300000):
    left = ([0] if phase == 0 else [0, 0])
    left += [v for _ in range(m) for v in (1, 0)] + [1, 1]
    l = deque(left)
    right = deque(map(int, word))
    scan, state = 0, phase
    for time in range(cap):
        if state == 5:
            if scan == 1:
                return "halt", time
            if time > 0 and not any(l):
                return "return", time
        instruction = RULES[state][scan]
        if instruction is None:
            raise AssertionError("unreachable")
        write, direction, state = instruction
        if direction == 1:
            l.appendleft(write)
            scan = right.popleft() if right else 0
        else:
            right.appendleft(write)
            scan = l.popleft() if l else 0
    raise RuntimeError("cap reached")


def test() -> None:
    randomizer = random.Random(20261106)
    for phase in (0, 4):
        rows = certify(phase, 15)["witnesses"]
        randomizer.shuffle(rows)
        subset = rows[: min(400, len(rows))]
        for prefix, kind, t0, t1, _, _ in subset:
            for _ in range(3):
                suffix = "".join(str(randomizer.getrandbits(1)) for _ in range(40))
                word = prefix + suffix
                a = raw_first_event(phase, 3, word)
                b = raw_first_event(phase, 7, word)
                if (a, b) != ((kind, t0), (kind, t1)):
                    raise AssertionError((phase, prefix, a, b))
                x, y = evaluate(phase, 3, word), evaluate(phase, 7, word)
                if x is None or y is None or not check(phase, x, y):
                    raise AssertionError((phase, prefix, x, y))
        print(f"phase={phase}: {3 * len(subset)} independent checks passed")


if __name__ == "__main__":
    test()
