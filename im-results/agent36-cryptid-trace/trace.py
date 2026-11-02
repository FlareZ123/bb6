"""Conditional BB(6) Cryptid D-start symbolic F-section tracker.

Machine: 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---
Source of seed: Agent31's blank36 (exact, Lean certified).
This is NOT a certified nonhalting result: macro compositions and new branches
must be independently proved against the unmodified raw machine.
"""
from collections import Counter
from dataclasses import dataclass
from hashlib import sha256
import sys

@dataclass(frozen=True)
class Section:
    n: int
    suffix: str
    time: int

def bit(s: str, i: int) -> str:
    return s[i] if i < len(s) else "0"

def canonical(n: int, s: str) -> tuple[int, str]:
    """Absorb leading ones into n; remove only inessential trailing zeros."""
    i = len(s) - len(s.lstrip("1"))
    return n + i, s[i:].rstrip("0")

def advance(st: Section) -> tuple[Section, str]:
    n, s, t = st.n, st.suffix, st.time
    assert n > 0 and bit(s, 0) == "0"
    if n % 3 == 2:
        k = (n - 2) // 3
        nn, ss = 8*k + 9, s[1:]
        dt, rule = 12*k*k + 49*k + 40, "B"
    elif n % 3 == 0:
        k = (n - 3) // 3
        i, q = 1, 0
        while bit(s, i) == "1" and bit(s, i+1) == "0":
            q += 1
            i += 2
        j = i
        while bit(s, j) == "1":
            j += 1
        ones = j - i
        r = ones // 3
        dt_common = 12*k*k + 49*k + 4*q + 12*r*r + (24*k + 55 + 6*q)*r
        if ones % 3 == 0:
            nn, ss = 8*k + 11 + 2*q + 8*r, s[j+1:]
            dt, rule = dt_common + 44, "A-pairs"
        elif ones % 3 == 1 and bit(s, j) == bit(s, j+1) == "0":
            nn, ss = 8*k + 13 + 2*q + 8*r, s[j+2:]
            dt, rule = dt_common + 48, "A-extra10"
        elif ones % 3 == 2 and bit(s, j) == bit(s, j+1) == "0":
            nn, ss = 8*k + 7 + 2*q + 8*r, "0" + "1"*6 + s[j+2:]
            dt, rule = dt_common + 54, "A-E-pairs"
        else:
            raise ValueError(f"A branch unresolved, ones={ones}, q={q}, suffix={s[:80]}")
    else:
        k = (n - 4) // 3
        i, q = 1, 0
        while bit(s, i) == "1" and bit(s, i+1) == "0":
            q += 1
            i += 2
        if bit(s, i) == "0":
            nn, ss = 8*k + 5, "0" + "1"*(2*q+6) + s[i+1:]
            dt, rule = 12*k*k + 49*k + 50 + 4*q, "E-pairs"
        elif all(bit(s, i+j) == "1" for j in range(3)):
            nn, ss = 8*k + 9, "01"*(q+2) + "0" + s[i+3:]
            dt, rule = 12*k*k + 49*k + 58 + 6*q, "E-triple"
        elif q >= 1 and "".join(bit(s, i+j) for j in range(4)) == "1100":
            nn = 8*k + 5
            ss = "0" + "1"*(2*q+2) + "0" + "1"*6 + s[i+4:]
            dt, rule = 12*k*k + 49*k + 60 + 4*q, "E-double"
        else:
            raise ValueError(f"E branch unresolved, q={q}, suffix={s[:80]}")
    nn, ss = canonical(nn, ss)
    return Section(nn, ss, t+dt), rule

def trace(count: int = 30000) -> None:
    # Allow decimal rendering of long integers in optional diagnostics.
    sys.set_int_max_str_digits(1000000)
    state = Section(9, "", 36)
    counts = Counter()
    digest = sha256()
    for i in range(count):
        state, rule = advance(state)
        counts[rule] += 1
        # Unambiguous integer-byte boundaries: ASCII separator and final LF.
        digest.update(state.n.to_bytes((state.n.bit_length()+7)//8, "big"))
        digest.update(b"|")
        digest.update(state.suffix.encode("ascii"))
        digest.update(b"|")
        digest.update(state.time.to_bytes((state.time.bit_length()+7)//8, "big"))
        digest.update(b"\n")
    print("sections:", count)
    print("unary bit length:", state.n.bit_length())
    print("step-count bit length:", state.time.bit_length())
    print("suffix:", repr(state.suffix))
    print("macro counts:", dict(counts))
    print("SHA256:", digest.hexdigest())

if __name__ == "__main__":
    trace()
