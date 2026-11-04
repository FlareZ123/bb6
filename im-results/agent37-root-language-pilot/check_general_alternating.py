"""Independent literal six-state-table regression for all-r A/E return families.

This parser shares no transition implementation with the Lean macros.  It checks
the FIRST *physical* F-on-zero return, primitive-step count, and the complete
blank-padded tape against the proposed all-natural identities.  Finite evidence
only: Lean original-source verification remains separately necessary.
"""
from random import Random

RLE = "1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---"
TABLE = {}
for state, row in enumerate(RLE.split("_")):
    for bit in (0, 1):
        code = row[3 * bit : 3 * bit + 3]
        TABLE[state, bit] = None if code == "---" else (
            int(code[0]),
            1 if code[1] == "R" else -1,
            ord(code[2]) - ord("A"),
        )


def first_physical_return(left: str, right: str, state: int, cap: int = 100000):
    """The initial scanned symbol is zero, and left/right are nearest-first."""
    ones = {-i - 1 for i, bit in enumerate(left) if bit == "1"}
    ones.update(i + 1 for i, bit in enumerate(right) if bit == "1")
    head = 0
    for elapsed in range(cap):
        scanned = int(head in ones)
        if state == 5 and scanned == 1:
            return "HALT", elapsed, None
        if elapsed > 0 and state == 5 and scanned == 0 and all(p >= head for p in ones):
            end = max(ones, default=head)
            tape = "".join("1" if p in ones else "0" for p in range(head + 1, end + 1))
            return "RETURN", elapsed, tape.rstrip("0")
        action = TABLE[state, scanned]
        if action is None:
            return "HALT", elapsed, None
        write, move, state = action
        (ones.add if write else ones.discard)(head)
        head += move
    return "TIMEOUT", cap, None


def check():
    rng = Random(202611041724)
    count_a = 0
    count_e = 0
    for m in range(13):
        for r in range(16):
            for tail_len in range(8):
                suffix = "".join(str(rng.getrandbits(1)) for _ in range(tail_len))
                left = "0" + "10" * m + "11"
                right = "110" + "10" * r + "111" + suffix
                expected = ("1" * (2 * m + 5) + "01" * (r + 2) + "0" + suffix).rstrip("0")
                observed = first_physical_return(left, right, 0)
                assert observed == ("RETURN", 2 * m + 6 * r + 24, expected), (
                    "A", m, r, suffix, observed
                )
                count_a += 1

    for k in range(8):
        for q in range(11):
            for r in range(13):
                for tail_len in range(4):
                    suffix = "".join(str(rng.getrandbits(1)) for _ in range(tail_len))
                    right = "1" * (3 * k + 4) + "0" + "10" * q + "110" + "10" * r + "111" + suffix
                    expected = (
                        "1" * (8 * k + 5) + "0" + "1" * (2 * q + 6) +
                        "01" * (r + 2) + "0" + suffix
                    ).rstrip("0")
                    observed = first_physical_return("", right, 5)
                    assert observed == ("RETURN", 12 * k * k + 49 * k + 68 + 4 * q + 6 * r, expected), (
                        "E", k, q, r, suffix, observed
                    )
                    count_e += 1
    print("RLE:", RLE)
    print("A m=0..12, r=0..15, suffix lengths=0..7:", count_a, "checks passed")
    print("E k=0..7, q=0..10, r=0..12, suffix lengths=0..3:", count_e, "checks passed")


if __name__ == "__main__":
    check()
