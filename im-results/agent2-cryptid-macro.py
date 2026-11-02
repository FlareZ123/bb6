#!/usr/bin/env python3
"""Reproduce finite BB(6) cryptid macro traces; no claim about blank-tape halting."""
from itertools import product

MACHINE = "1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---"
TRANSITIONS = [(s[:3], s[3:]) for s in MACHINE.split("_")]

def macro(n: int, suffix: str, fuel: int = 200_000):
    """Advance to the next F/0 with a genuinely blank physical left half-tape."""
    assert n >= 2 and (not suffix or suffix.startswith("0"))
    assert set(suffix) <= {"0", "1"}
    ones = set(range(1, n + 1))
    ones.update(n + 1 + i for i, b in enumerate(suffix) if b == "1")
    head, state = 0, 5
    for t in range(fuel):
        if t and state == 5 and head not in ones and all(pos >= head for pos in ones):
            x = head + 1
            while x in ones:
                x += 1
            first_suffix = x
            last_one = max(ones, default=0)
            new_suffix = "".join("1" if j in ones else "0"
                                 for j in range(first_suffix, last_one + 1))
            return (first_suffix - head - 1, new_suffix, t, head)
        instruction = TRANSITIONS[state][int(head in ones)]
        if instruction == "---":
            return ("HALT", t, head)
        if instruction[0] == "1":
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if instruction[1] == "R" else -1
        state = ord(instruction[2]) - ord("A")
    return ("TIMEOUT", fuel)

def path(n: int, suffix: str, k: int):
    results = []
    for _ in range(k):
        branch = ("A", "E", "B")[n % 3]
        result = macro(n, suffix)
        results.append((branch, n, suffix, result))
        if len(result) != 4:
            break
        n, suffix = result[:2]
    return results

def check():
    expected = [
        (4, "011", (3, "01111010101", 96, -6)),
        (3, "01111010101", (27, "", 127, -11)),
        (31, "011", (75, "01111010101", 1509, -51)),
        (75, "01111010101", (219, "", 8791, -131)),
    ]
    for n, suffix, target in expected:
        actual = macro(n, suffix)
        assert actual == target, (n, suffix, actual, target)
        print(f"A({n}, {suffix!r}) -> {actual}")
    for n in (4, 31):
        p = path(n, "011", 3)
        print(f"n={n}, branch sequence: {[x[0] for x in p]}")
    # A mere F/0 with nonblank cells left of the head is not an A-section return.\n    # The earlier 91-step n=4 marker was such a false return.\n    for k in range(1, 20):
        n = 3 * k + 1
        result = macro(n, "011011")
        assert result == ("HALT", 12*k*k+17*k+69, n-2), (k, result)
    print("Quadratic halting-time pattern checked for k=1,...,19.")

if __name__ == "__main__":
    check()
