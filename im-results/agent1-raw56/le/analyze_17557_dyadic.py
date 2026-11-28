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

Between consecutive C_n checkpoints, blank-head A returns also exhibit an
exact finite recursive branch grammar in the checked prefix. Group returns in
triads and write A for D-branch pattern IZI (I = first D read is 1, Z = first
D read is 0) and B for ZZI. The observed epoch words satisfy
  W_2 = ABBA
  W_(n+1) = sigma(W_n),  sigma(A)=ABA, sigma(B)=BBA.
Hence the checked epoch has 4*3^(n-2) triads and 4*3^(n-1) blank-head returns.
This substitution law is still conjectural beyond the simulated prefix.

This script performs one literal primitive-step simulation through T(11),
asserting every checkpoint, every intervening branch triad through epoch 10,
and failing if the undefined F1 slot is queried.
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


def sigma(word):
    return "".join("ABA" if c == "A" else "BBA" for c in word)


def main():
    trans = parse(TABLE)
    tape = set()
    q = 0
    h = 0
    checkpoints = {T(n): n for n in range(2, MAX_N+1)}
    final = T(MAX_N)

    # Segment alphabet: I means the D sweep first reads 1; Z means it first
    # reads 0. Each segment starts and ends at state A scanning 0.
    segment_epoch = None
    segment_d0 = False
    segments = {n: [] for n in range(2, MAX_N)}

    for t in range(final + 1):
        b = 1 if h in tape else 0

        if q == 0 and b == 0:
            if segment_epoch is not None:
                segments[segment_epoch].append("Z" if segment_d0 else "I")
            segment_d0 = False
            segment_epoch = None
            for n in range(2, MAX_N):
                if T(n) <= t < T(n+1):
                    segment_epoch = n
                    break

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

        if q == 3 and b == 0:
            segment_d0 = True
        mv = trans.get((q, b))
        assert mv is not None, ("queried undefined slot", t, q, b, h)
        w, d, q = mv
        if w:
            tape.add(h)
        else:
            tape.discard(h)
        h += d

    previous = None
    for n in range(2, MAX_N):
        seg = segments[n]
        assert len(seg) == 4*(3**(n-1)), (n, len(seg))
        assert len(seg) % 3 == 0
        word = ""
        for i in range(0, len(seg), 3):
            triad = "".join(seg[i:i+3])
            if triad == "IZI":
                word += "A"
            elif triad == "ZZI":
                word += "B"
            else:
                raise AssertionError(("unexpected triad", n, i//3, triad))
        assert len(word) == 4*(3**(n-2))
        if n == 2:
            assert word == "ABBA"
        else:
            assert word == sigma(previous), (n, word, sigma(previous))
        assert word.count("A") == word.count("B") == 2*(3**(n-2))
        print(f"W_{n}: triads={len(word)} A={word.count('A')} B={word.count('B')}")
        previous = word

    print(
        "PASS finite dyadic + substitution audit through "
        f"C_{MAX_N} at {final:,} primitive steps; infinite recurrence remains conjectural"
    )


if __name__ == "__main__":
    main()
