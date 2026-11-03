"""Independent sparse raw-table checker for macro_engine.py.

No dependence on Lean or macro semantics in the raw-step implementation.
Finite evidence only: verifies successful-step counts and complete F/0 tapes.
"""
from collections import Counter
import random
from macro_engine import Config, canonical, step

RLE = "1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---"
TABLE = {}
for state, row in enumerate(RLE.split("_")):
    for bit in (0, 1):
        token = row[3*bit:3*bit+3]
        TABLE[state,bit] = None if token == "---" else (
            int(token[0]), 1 if token[1] == "R" else -1, ord(token[2])-65
        )


def raw(c, cap=1000000):
    ones = set(range(1,c.n+1)) | {
        c.n+i+1 for i, b in enumerate(c.suffix) if b == "1"
    }
    head = 0
    state = 5
    for t in range(1,cap+1):
        read = int(head in ones)
        action = TABLE[state,read]
        if action is None:
            return t-1,"HALT",None
        write,direction,state = action
        (ones.add if write else ones.discard)(head)
        head += direction
        if state == 5 and head not in ones and (not ones or min(ones)>head):
            last = max(ones) if ones else head
            word = "".join("1" if i in ones else "0" for i in range(head+1,last+1)).rstrip("0")
            unary = len(word)-len(word.lstrip("1"))
            return t,"RETURN",canonical(unary,word[unary:])
    return cap,"TIMEOUT",None


def test():
    rng = random.Random(70837)
    checked = Counter()
    unsupported = 0
    errors = []
    for a in range(2,48):
        for _ in range(110):
            size = rng.randrange(0,24)
            suffix = "".join(str(rng.getrandbits(1)) for _ in range(size)).rstrip("0")
            lead = len(suffix)-len(suffix.lstrip("1"))
            c = Config(a+lead,suffix[lead:])
            rule,t,expected = step(c)
            if t is None:
                unsupported += 1
                continue
            if t > 1000000:
                continue
            observed_t,status,observed = raw(c)
            checked[rule] += 1
            halted = rule.endswith("_halt")
            bad = (status != ("HALT" if halted else "RETURN") or observed_t != t
                   or (not halted and observed != expected))
            if bad:
                errors.append((c,rule,t,expected,observed_t,status,observed))
    print("Table:",RLE)
    print("Generated=5060 checked=",sum(checked.values()),"unsupported=",unsupported,
          "mismatches=",len(errors))
    print("Branch coverage:",dict(sorted(checked.items())))
    for issue in errors[:20]:
        print("MISMATCH",issue)
    assert not errors


if __name__ == "__main__":
    test()
