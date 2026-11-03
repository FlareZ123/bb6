"""Conservative D0 cryptid return-section interpreter.

Every recognized transition is derived from named, previously source-certified
six-state Lean macro families. This Python program is NOT itself a Lean proof.
Original table: 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---
"""
from collections import Counter
from dataclasses import dataclass


@dataclass(frozen=True)
class Config:
    n: int
    suffix: str

    def __post_init__(self):
        assert self.n >= 2
        assert not self.suffix or self.suffix[0] == "0"
        assert not self.suffix.endswith("0")


def canonical(n: int, suffix: str) -> Config:
    suffix = suffix.rstrip("0")  # only infinite-blank physical equivalence
    count = len(suffix) - len(suffix.lstrip("1"))
    return Config(n + count, suffix[count:])


def step(c: Config):
    """(source-family, successful primitive steps, physical next F0 Config).

    A halt returns next=None. Missing source grammar returns (tag,None,None).
    Source frozen-halt time is one step greater than raw successful transitions.
    """
    n, s = c.n, c.suffix
    if n % 3 == 2:
        k = (n - 2) // 3
        return "B", 12*k*k + 49*k + 40, canonical(8*k + 9, s[1:] if s else "")

    if n % 3 == 0:
        k = (n - 3) // 3
        m = 4*k + 3
        p = 12*k*k + 41*k + 32
        v = s[1:] if s else ""
        cost = 0
        while True:
            if not v or v[0] == "0":
                return "A_code_close", p+cost+2*m+6, canonical(2*m+5, v[1:] if v else "")
            if v.startswith("10") or v == "1":
                cost += 2
                m += 1
                v = v[2:] if len(v) >= 2 else ""
                continue
            if v.startswith("111"):
                cost += 6*m+41
                m += 4
                v = v[3:]
                continue
            if v.startswith("1100") or v in ("11", "110"):
                return "A1100", p+cost+2*m+16, canonical(2*m+1, "0"+"1"*6+(v[4:] if len(v)>4 else ""))
            if v.startswith("110111"):
                return "A110111", p+cost+2*m+24, canonical(2*m+5, "01010"+v[6:])
            if v.startswith("1101101100"):
                return "A_halt", p+cost+68, None
            return "A_unresolved:"+v[:30], None, None

    k = (n - 4) // 3
    p = 12*k*k+49*k
    v = s[1:] if s else ""
    if not v or v[0] == "0":
        return "E00", p+50, canonical(8*k+5, "0"+"1"*6+(v[1:] if v else ""))

    q = 0
    while v.startswith("10"):
        q += 1
        v = v[2:]
    if v == "1":  # implicit zero completes a final 10 token
        q += 1
        v = ""
    if not v or v[0] == "0":
        return "E_pairs", p+50+4*q, canonical(8*k+5, "0"+"1"*(2*q+6)+(v[1:] if v else ""))
    if v.startswith("111"):
        return "E_triple_pairs", p+58+6*q, canonical(8*k+9, "01"*(q+2)+"0"+v[3:])
    if v.startswith("1100") or v in ("11", "110"):
        tail = v[4:] if len(v) > 4 else ""
        if q == 0:
            return "E1100", p+96, canonical(8*k+3, "011110101010"+tail)
        return "E_pairs_1100", p+60+4*q, canonical(
            8*k+5, "0"+"1"*(2*q+2)+"0"+"1"*6+tail
        )
    if v.startswith("110111") and q == 0:
        return "E110111", p+68, canonical(8*k+3, "110"+"1"*6+"01010"+v[6:])
    if v.startswith("1101100") and q == 0:
        return "E_halt", 12*k*k+41*k+98, None
    return f"E_unresolved(q={q}):{v[:30]}", None, None


def run(seed: int, sections: int = 20000):
    c = Config(seed, "")
    successful_steps = 0
    counts = Counter()
    for i in range(sections):
        label, cost, nxt = step(c)
        counts[label] += 1
        if cost is None or nxt is None:
            print(f"seed={seed} stopped at section={i} label={label}")
            print(f"  n_bits={c.n.bit_length()} n_mod_27={c.n%27} suffix={c.suffix}")
            print(f"  previous_steps_bits={successful_steps.bit_length()}")
            return c, label, counts
        successful_steps += cost
        c = nxt
    print(f"seed={seed} sections={sections} n_bits={c.n.bit_length()} " +
          f"suffix={c.suffix} successful_steps_bits={successful_steps.bit_length()}")
    print("  families:", dict(counts))
    return c, "limit", counts


if __name__ == "__main__":
    for seed in (5, 9, 15, 39):
        run(seed)
