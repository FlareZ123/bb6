"""Literal TM63 six-state original-step regression of Lean CountedOdd theorem."""
from random import Random

RLE = "1RB---_1LC0RF_1RE0LD_0LC1RB_1RA1RE_1RE0RD"
RULES = []
for pair in RLE.split("_"):
    transitions = []
    for k in (0, 3):
        act = pair[k:k + 3]
        if act == "---":
            transitions.append(None)
        else:
            transitions.append((int(act[0]), 1 if act[1] == "R" else -1, ord(act[2]) - ord("A")))
    RULES.append(transitions)


def rc(c):
    return [0, 1, 1, 1, 0, 0, 1, 1, 1] + [1] * (3 * c)


def physical(left, head, right):
    marks = {-i for i, b in enumerate(left, 1) if b}
    if head:
        marks.add(0)
    marks.update(i for i, b in enumerate(right, 1) if b)
    return marks


def check(left, c):
    bits = physical([0, 1] + left, 0, rc(c))
    state = 3
    pos = 0
    cost = 48 + 12 * c
    for t in range(cost):
        action = RULES[state][int(pos in bits)]
        assert action is not None, ("unexpected halted intermediate", t, left, c)
        write, direction, state = action
        if write:
            bits.add(pos)
        else:
            bits.discard(pos)
        pos += direction
    assert pos == 0 and state == 3, ("wrong endpoint state/head", left, c, pos, state)
    expected = physical([1, 1] + left, 1, rc(c + 1))
    assert bits == expected, ("different output tape", left, c, bits ^ expected)


def main():
    rng = Random(2026110302)
    n = 0
    steps = 0
    for c in range(21):
        for _ in range(100):
            left = [rng.randrange(2) for _ in range(rng.randrange(45))]
            check(left, c)
            n += 1
            steps += 48 + 12 * c
    print(f"PASS {n} original table whole-tape tests, {steps} primitive transitions; source={RLE}")


if __name__ == "__main__":
    main()
