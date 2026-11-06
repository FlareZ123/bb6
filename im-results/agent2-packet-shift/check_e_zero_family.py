"""Independent primitive simulator for exceptional D-family E returns.

Turing machine: 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---.
The first return is physically blank-left F/0, with implicit zero padding.
This checks finite samples only; universal endpoint claims are Lean theorems.
"""
from itertools import product

TABLE = (
    ((1, 1, 1), (0, 1, 4)),
    ((1, -1, 2), (0, 1, 0)),
    ((1, -1, 0), (1, -1, 3)),
    ((1, -1, 2), (1, -1, 5)),
    ((0, -1, 2), (0, -1, 1)),
    ((1, -1, 4), None),
)


def first_event(right, maxsteps=100000):
    tape = {i + 1: 1 for i, bit in enumerate(right) if bit == "1"}
    head, state = 0, 5
    for t in range(1, maxsteps + 1):
        action = TABLE[state][tape.get(head, 0)]
        if action is None:
            return "halt", t - 1, ""
        write, delta, state = action
        if write:
            tape[head] = 1
        else:
            tape.pop(head, None)
        head += delta
        if state == 5 and head not in tape and all(p >= head for p in tape):
            last = max(tape, default=head)
            word = "".join(str(tape.get(p, 0)) for p in range(head + 1, last + 1))
            return "return", t, word.rstrip("0")
    return "timeout", maxsteps, ""


def predicted(k, q, r, tail):
    a = 3 * k + 4
    word = "1" * a + "0" + "10" * q + "110" + "10" * r + "0" + tail
    if q == 0:
        time = 12 * k * k + 49 * k + 96 + 4 * r
        output = "1" * (8 * k + 3) + "011110101010" + "1" * (2 * r) + tail
    elif q == 1:
        time = 12 * k * k + 49 * k + 64 + 4 * r
        output = "1" * (8 * k + 3) + "11011110" + "1" * (2 * r + 6) + tail
    else:
        time = 12 * k * k + 49 * k + 60 + 4 * q + 4 * r
        output = (
            "1" * (8 * k + 5) + "0" + "1" * (2 * q + 2)
            + "0" + "1" * (2 * r + 6) + tail
        )
    return word, time, output.rstrip("0")


def main():
    cases = 0
    tails = ["", "0", "1", "01", "11", "000", "1010111", "110100101"]
    for k, q, r, tail in product(range(8), range(6), range(13), tails):
        word, time, output = predicted(k, q, r, tail)
        observed = first_event(word, maxsteps=time + 1)
        assert observed == ("return", time, output), (
            k, q, r, tail, observed, time, output
        )
        cases += 1
    print(f"PASS {cases:,} first-physical-return instances")


if __name__ == "__main__":
    main()
