#!/usr/bin/env python3
"""Independent literal-table replay. This is computation, not a proof certificate."""
TABLES = (
    "1RB---_1RC0RA_0RD0LF_1LD1RE_0RB0LF_1LC0LF",
    "1RB0LA_1RC---_0RD0RB_1LD1RE_0LA0LF_1LB1LE",
)
def replay(table):
    raw = table.replace("_", "")
    rules = [raw[i:i+3] for i in range(0, 36, 3)]
    q = p = n = lo = hi = 0
    ones = set()
    while True:
        read = int(p in ones)
        rule = rules[2*q+read]
        n += 1
        if rule == "---":
            break
        if rule[0] == "1":
            ones.add(p)
        else:
            ones.discard(p)
        p += 1 if rule[1] == "R" else -1
        q = ord(rule[2])-65
        lo, hi = min(lo, p), max(hi, p)
    def delay(start):
        state, seen, d = start, set(), 0
        while state not in seen:
            if state == 0:
                return d
            seen.add(state)
            rule = rules[2*state]
            if rule == "---" or rule[0] != "0":
                return None
            state, d = ord(rule[2])-65, d+1
        return None
    ds = sorted({d for s in range(6) if (d := delay(s)) is not None})
    return n, chr(65+q), read, p, hi-lo+1, ds, n+max(ds)
if __name__ == "__main__":
    results = [replay(t) for t in TABLES]
    expected = [
        (6659487, "A", 1, 382, 550, [0], 6659487),
        (1296925, "B", 1, -22, 1479, [0, 1], 1296926),
    ]
    for table, result, target in zip(TABLES, results, expected):
        print(table, result)
        assert result == target
