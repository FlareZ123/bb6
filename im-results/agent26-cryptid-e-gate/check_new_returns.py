"""Direct raw-step regression for Agent26 D-Cryptid return theorems.

Independent of Lean; enumerates the literal 12-rule Turing machine.
Checks exact first physically blank-left F-on-zero return and full physical
right tape after removing only implicit trailing zeros.
"""
import random
from dataclasses import dataclass

TABLE = "1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---"
RULES = [
    [None if b[i:i+3] == "---" else
     (int(b[i]), 1 if b[i+1] == "R" else -1, ord(b[i+2])-65)
     for i in (0, 3)]
    for b in TABLE.split("_")
]


@dataclass(frozen=True)
class Source:
    state: int
    left_near_first: str
    right: str


def first_return(source: Source, limit: int):
    tape = {-i-1: 1 for i, x in enumerate(source.left_near_first) if x == "1"}
    tape.update({i+1: 1 for i, x in enumerate(source.right) if x == "1"})
    head, state = 0, source.state
    for elapsed in range(1, limit+1):
        rule = RULES[state][head in tape]
        if rule is None:
            return "halt", elapsed-1, ""
        write, direction, state = rule
        if write:
            tape[head] = 1
        else:
            tape.pop(head, None)
        head += direction
        if state == 5 and head not in tape and not any(x < head for x in tape):
            bits = "".join("1" if x in tape else "0"
                           for x in range(head+1, max(tape, default=head)+1))
            return "F0", elapsed, bits.rstrip("0")
    return "cap", limit, ""


def token_code(w: str):
    encoded, delta, cost = "", 0, 0
    for bit in w:
        if bit == "0":
            encoded += "10"
            cost += 2
            delta += 1
        else:
            encoded += "111"
            cost += 6*delta+41
            delta += 4
    return encoded, delta, cost


def test():
    random.seed(20261104)
    counts = {"A10": 0, "A8": 0, "A12zero": 0, "Epair": 0, "Acode": 0}
    for m in range(24):
        for i in range(13):
            suffix = "".join(random.choices("01", k=i))
            left = "0"+"10"*m+"11"
            cases = [
                ("A10", left, "1101010111", 2*m+36, "1"*(2*m+5)+"010101010"),
                ("A8", left, "11010111", 2*m+30, "1"*(2*m+5)+"0101010"),
                ("A12zero", "0"+"10"*(m+1)+"11", "110101010100",
                 2*m+34, "1"*(2*m+3)+"0"+"1"*14),
            ]
            for tag, leftbits, packet, time, outcome in cases:
                actual = first_return(Source(0, leftbits, packet+suffix), time+4)
                expected = ("F0", time, (outcome+suffix).rstrip("0"))
                assert actual == expected, (tag, m, suffix, actual, expected)
                counts[tag] += 1

    for k in range(15):
        for q in range(13):
            for i in range(5):
                suffix = "".join(random.choices("01", k=i))
                n = 3*k+4
                time = 12*k*k+49*k+80+4*q
                start = Source(5, "", "1"*n+"0"+"10"*q+"1101010111"+suffix)
                actual = first_return(start, time+4)
                outcome = "1"*(8*k+5)+"0"+"1"*(2*q+6)+"010101010"+suffix
                expected = ("F0", time, outcome.rstrip("0"))
                assert actual == expected, ("Epair", k, q, suffix, actual, expected)
                counts["Epair"] += 1

    for k in range(8):
        for width in range(5):
            for i in range(10):
                w = "".join(random.choices("01", k=width))
                suffix = "".join(random.choices("01", k=i))
                encoded, delta, partial = token_code(w)
                cost = partial+6*(4*k+3)*w.count("1")
                m = 4*k+3+delta
                time = 12*k*k+41*k+32+cost+2*m+36
                start = Source(5, "", "1"*(3*k+3)+"0"+encoded+
                               "1101010111"+suffix)
                actual = first_return(start, time+6)
                outcome = "1"*(2*m+5)+"010101010"+suffix
                expected = ("F0", time, outcome.rstrip("0"))
                assert actual == expected, ("Acode", k, w, suffix, actual, expected)
                counts["Acode"] += 1

    print("PASS: 2,311 literal primitive-machine configurations; by branch:", counts)


if __name__ == "__main__":
    test()
