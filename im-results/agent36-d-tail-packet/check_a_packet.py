"""Independent primitive-step checks of the D0 physical F/0 packet grammar.

Run: python check_a_packet.py
This script parses the literal 12-entry six-state original machine. It verifies
finite examples only; universal results need source-level Lean import.
"""
from collections import Counter

RLE = "1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---"
TABLE = {}
for state, row in enumerate(RLE.split("_")):
    for bit in (0, 1):
        code = row[3 * bit:3 * bit + 3]
        TABLE[state, bit] = None if code == "---" else (
            int(code[0]), 1 if code[1] == "R" else -1, ord(code[2]) - 65
        )
assert len(TABLE) == 12 and TABLE[5, 1] is None


def canonical(word):
    word = word.rstrip("0")
    leading = len(word) - len(word.lstrip("1"))
    return leading, word[leading:]


def raw_first_return(a, suffix, cap=300000):
    """Physical F/0 and left blank. Return (kind, successful steps, endpoint)."""
    ones = set(range(1, a + 1))
    ones.update(a + i + 1 for i, bit in enumerate(suffix) if bit == "1")
    head, state = 0, 5
    for elapsed in range(1, cap + 1):
        action = TABLE[state, int(head in ones)]
        if action is None:
            return "HALT", elapsed - 1, None
        write, direction, state = action
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += direction
        if state == 5 and head not in ones and (not ones or min(ones) > head):
            end = max(ones, default=head)
            word = "".join("1" if i in ones else "0" for i in range(head + 1, end + 1))
            prefix, tail = canonical(word)
            return "RETURN", elapsed, (prefix, tail)
    return "TIMEOUT", cap, None


def predicted_A_110_triple(k, tokens, triples, h, y):
    """A with arbitrary pair/triple precode followed by 110(10)^h111."""
    n = 3 * k + 3
    s = "0" + "10" * tokens + "111" * triples + "110" + "10" * h + "111" + y
    t = (12*k*k + 49*k + 62 + 4*tokens + 12*triples*triples
         + (24*k + 55 + 6*tokens)*triples + 6*h)
    output = canonical("1" * (8*k + 11 + 2*tokens + 8*triples)
                       + "01" * (h + 2) + "0" + y)
    return n, s, t, output


def predicted_A_packet(k, q, r, p_mod_3):
    """M(3k+3,q,3r+phase;01010111) returns to the regular L class."""
    s = "01" * q + "0" + "1" * (3*r + p_mod_3) + "01010111"
    common = (12*k*k + 49*k + 4*q + 12*r*r
              + (24*k + 55 + 6*q)*r)
    if p_mod_3 == 0:
        return 3*k+3, s, common+44, (8*k+12+2*q+8*r, "010111")
    if p_mod_3 == 1:
        t = 12*k*k + 73*k + 141 + 10*q + 12*r*r + (24*k+79+6*q)*r
        return 3*k+3, s, t, (8*k+25+2*q+8*r, "")
    return 3*k+3, s, common+74, (8*k+11+2*q+8*r, "01010101")


def verify_case(args):
    n, suffix, time, target = args
    actual = raw_first_return(n, suffix, max(300000, time + 3))
    assert actual == ("RETURN", time, target), (args, actual)


def main():
    count = Counter()
    tails = ["", "0", "1", "010", "111", "001", "1010110", "00101010", "1110111"]
    for k in range(6):
        for q in range(5):
            for r in range(5):
                for h in range(5):
                    for y in tails:
                        verify_case(predicted_A_110_triple(k, q, r, h, y))
                        count["A_110_pairs_triple"] += 1
    for k in range(10):
        for q in range(9):
            for r in range(9):
                for phase in range(3):
                    verify_case(predicted_A_packet(k, q, r, phase))
                    count[f"A_packet_p{phase}"] += 1
    # The two-tail trial grammar L union M(-;0111111 or 01010111)
    # is already falsified by this exact arbitrary-k E pair branch.
    for k in range(13):
        n = 3*k+4
        source = "001010111"
        endpoint = (8*k+5, "01111111010111")
        verify_case((n, source, 12*k*k+49*k+50, endpoint))
        count["E_two_tail_counterexamples"] += 1
    print("PASS:", dict(count), "all original raw-table first-return checks")
    print("Smallest grammar counterexample: I_4(001010111) ->")
    print("  I_5(01111111010111) after exactly 50 primitive transitions")
    print("All sample results remain finite verification, not blank-origin reachability.")


if __name__ == "__main__":
    main()
