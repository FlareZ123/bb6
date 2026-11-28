#!/usr/bin/env python3
"""Exact finite checkpoint audit for unresolved Raw56 leaf 17557.

Literal partial machine:
  1RB1LA_1RC1RB_0RD0RC_1LD1LE_1LF0LE_0LA---

The experiment checks a dyadic blank-run family C_n.  It is deliberately
NOT a nonhalting proof: only n=2..11 are simulated.  The conjectural infinite
recurrence is recorded because the family is exact and highly structured.

At time
  T(n) = 4*4^n + 8*3^(n-1) - 7*2^n - 1
the observed configuration C_n has state A, head h(n)=5-2^(n+2) on a blank,
blank tape strictly to its left, and to the right exactly
  1^(2^n-2) 0 1^(2^(n+1)-3) 0 1^(2^(n+1)-1).
Thus the conjectural epoch cost is
  T(n+1)-T(n) = 12*4^n + 16*3^(n-1) - 7*2^n.

This script performs one literal primitive-step simulation through T(11),
asserting every checkpoint exactly and failing if the undefined F1 slot is
queried.
"""

TABLE = "1RB1LA_1RC1RB_0RD0RC_1LD1LE_1LF0LE_0LA---"
MAX_N = 11


def parse(table):
    trans = {}
    for q, pair in enumerate(table.split("_")):
        for b in (0, 1):
            s = pair[3*b:3*b+3]
            if s == "---":
                continue
            trans[q, b] = (int(s[0]), 1 if s[1] == "R" else -1, ord(s[2])-65)
    return trans


def T(n):
    assert n >= 1
    return 4*(4**n) + 8*(3**(n-1)) - 7*(2**n) - 1


def expected(n):
    h = 5 - 2**(n+2)
    tape = set()
    p = h + 1
    for width in (2**n - 2,):
        tape.update(range(p, p + width))
        p += width + 1
    width = 2**(n+1) - 3
    tape.update(range(p, p + width))
    p += width + 1
    width = 2**(n+1) - 1
    tape.update(range(p, p + width))
    return h, tape


def main():
    trans = parse(TABLE)
    tape = set()
    q = 0
    h = 0
    checkpoints = {T(n): n for n in range(2, MAX_N+1)}
    final = T(MAX_N)

    for t in range(final + 1):
        n = checkpoints.get(t)
        if n is not None:
            eh, et = expected(n)
            assert q == 0, (n, t, "state", q)
            assert h == eh, (n, t, "head", h, eh)
            assert h not in tape, (n, t, "head not blank")
            assert tape == et, (n, t, "tape mismatch")
            if n < MAX_N:
                cost = T(n+1) - T(n)
                formula = 12*(4**n) + 16*(3**(n-1)) - 7*(2**n)
                assert cost == formula
            print(
                f"C_{n}: t={t} head={h} right_edge={max(tape)} "
                f"ones={len(tape)}"
            )

        if t == final:
            break
        b = 1 if h in tape else 0
        mv = trans.get((q, b))
        assert mv is not None, ("queried undefined slot", t, q, b, h)
        w, d, q = mv
        if w:
            tape.add(h)
        else:
            tape.discard(h)
        h += d

    print(
        "PASS finite dyadic checkpoint audit through "
        f"C_{MAX_N} at {final:,} primitive steps; infinite recurrence remains conjectural"
    )


if __name__ == "__main__":
    main()
