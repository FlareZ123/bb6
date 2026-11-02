"""Conditional multi-root Cryptid F-section tracker, using source-verified rules.

D0 blank starts A,B,C,F reach F-on-zero unary seeds 9,5,15,39 at
primitive times 36,15,92,403 respectively (Agent 3's source Lean).
All transitions below have universal, original-machine Lean proofs in
Agent31/32/35/36 modules, but this Python composition is only empirical.
In particular it does not certify an infinite blank trajectory or BB(6).
"""

from collections import Counter
from dataclasses import dataclass
from hashlib import sha256
import sys

sys.set_int_max_str_digits(1000000)

# Common D0-table start state, unary seed, primitive offset, rooted name.
ROOTS = (
    ("D0-A", 9, 36),
    ("D3-B", 5, 15),
    ("D2-C", 15, 92),
    ("D1-F", 39, 403),
)

@dataclass(frozen=True)
class Section:
    n: int
    suffix: str
    time: int


def bit(s: str, i: int) -> str:
    return s[i] if i < len(s) else "0"


def canonical(n: int, s: str) -> tuple[int, str]:
    s = s.rstrip("0")
    lead = len(s) - len(s.lstrip("1"))
    return n + lead, s[lead:]


def advance(st: Section) -> tuple[Section, str]:
    """One conditional F return with exact source-macro primitive cost."""
    n, s, t = st.n, st.suffix, st.time
    assert n > 0 and bit(s, 0) == "0"
    if n % 3 == 2:
        k = (n - 2) // 3
        nn, ss = 8 * k + 9, s[1:]
        dt, rule = 12 * k * k + 49 * k + 40, "B"
    elif n % 3 == 0:
        k = (n - 3) // 3
        i, inc, cost, m = 1, 0, 0, 4 * k + 3
        while True:
            if bit(s, i) == "0":
                nn, ss = 8 * k + 11 + 2 * inc, s[i + 1:]
                dt = 12 * k * k + 41 * k + 32 + cost + 2 * m + 6
                rule = "A-close"
                break
            if bit(s, i + 1) == "0":
                i, inc, cost, m = i + 2, inc + 1, cost + 2, m + 1
                continue
            if bit(s, i + 2) == "1":
                i, inc, cost, m = i + 3, inc + 4, cost + 6 * m + 41, m + 4
                continue
            # After the exact token-code prefix, the remaining gate is 110...
            if bit(s, i + 3) == "0":
                nn, ss = 8 * k + 7 + 2 * inc, "0" + "1" * 6 + s[i + 4:]
                dt = 12 * k * k + 41 * k + 32 + cost + 2 * m + 16
                rule = "A-double"
                break
            if all(bit(s, i + j) == "1" for j in range(3, 9)) and bit(s, i + 9) == "0":
                nn, ss = 8 * k + 11 + 2 * inc, "010101110" + s[i + 10:]
                dt = 12 * k * k + 41 * k + 32 + cost + 2 * m + 24
                rule = "A-six"
                break
            raise ValueError(f"A gate unavailable: n_bits={n.bit_length()}, suffix={s[:100]!r}")
    else:
        k = (n - 4) // 3
        i, q = 1, 0
        while bit(s, i) == "1" and bit(s, i + 1) == "0":
            i, q = i + 2, q + 1
        if bit(s, i) == "0":
            nn, ss = 8 * k + 5, "0" + "1" * (2 * q + 6) + s[i + 1:]
            dt, rule = 12 * k * k + 49 * k + 50 + 4 * q, "E-pairs"
        elif all(bit(s, i + j) == "1" for j in range(3)):
            nn, ss = 8 * k + 9, "01" * (q + 2) + "0" + s[i + 3:]
            dt, rule = 12 * k * k + 49 * k + 58 + 6 * q, "E-triple"
        elif q >= 1 and "".join(bit(s, i + j) for j in range(4)) == "1100":
            nn = 8 * k + 5
            ss = "0" + "1" * (2 * q + 2) + "0" + "1" * 6 + s[i + 4:]
            dt, rule = 12 * k * k + 49 * k + 60 + 4 * q, "E-double"
        elif q == 0 and "".join(bit(s, i + j) for j in range(4)) == "1100":
            nn, ss = 8 * k + 3, "011110101010" + s[i + 4:]
            dt, rule = 12 * k * k + 49 * k + 96, "E-zero-double"
        else:
            raise ValueError(f"E gate unavailable: n_bits={n.bit_length()}, suffix={s[:100]!r}")
    nn, ss = canonical(nn, ss)
    return Section(nn, ss, t + dt), rule


def trace(name: str, seed: int, offset: int, count: int = 30000) -> None:
    state = Section(seed, "", offset)
    counts = Counter()
    digest = sha256()
    for i in range(count):
        try:
            state, rule = advance(state)
        except ValueError as exc:
            print(f"{name}: stopped at macro {i}: {exc}")
            break
        counts[rule] += 1
        digest.update(state.n.to_bytes((state.n.bit_length() + 7) // 8, "big"))
        digest.update(b"|")
        digest.update(state.suffix.encode("ascii"))
        digest.update(b"|")
        digest.update(state.time.to_bytes((state.time.bit_length() + 7) // 8, "big"))
        digest.update(b"\n")
    print(f"{name}: macros={sum(counts.values())}, n_bits={state.n.bit_length()}, "
          f"time_bits={state.time.bit_length()}, suffix={state.suffix!r}")
    print(f"{name}: counts={dict(counts)}")
    print(f"{name}: SHA256={digest.hexdigest()}")


if __name__ == "__main__":
    for root, seed, offset in ROOTS:
        trace(root, seed, offset)
