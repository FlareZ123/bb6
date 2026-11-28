#!/usr/bin/env python3
"""Finite exact renormalization audit for Raw56 leaf 17557.

This is evidence for, not a proof of, the infinite nonhalting recurrence.

At A-on-blank triad boundaries in epoch n, write the zipper sides as alternating
run-length lists (near-to-far on the left; near-to-far on the right).  The
observed level-raising map rho sends every boundary k in epoch n to boundary
3*k in epoch n+1.  Since W_(n+1)=sigma(W_n), sigma(A)=ABA and sigma(B)=BBA,
this is the finite conjugacy pattern needed for an inductive proof.

The right map is a fixed typed run transformation.  For
  1^a1 0^z1 1^a2 0^z2 ... 1^am
with m>=2:
  a1 -> 2*a1+2
  z1 -> 2*z1-1
  if m=2: a2 -> 2*a2+4
  if m>=3: a2 -> 2*a2+3, z2 -> 2*z2-1,
            interior ai -> 2*ai, interior zi -> 2*zi+1,
            final am -> 2*am+1.

On the left, every 1-run doubles.  Every reachable 0-run except the fixed
anchor 3 has a unique signed-residue representation z=8*q+s with
s in {-1,0,1,2}; rho sends it to 16*q+s.  The anchor 3 stays 3.

The literal primitive simulator checks all corresponding boundaries for
levels 2->3 through 6->7 (1+4+12+36+108+324 lower macro transitions).
"""

TABLE = "1RB1LA_1RC1RB_0RD0RC_1LD1LE_1LF0LE_0LA---"
MAX_LEVEL = 7


def parse(table):
    out = {}
    for q, pair in enumerate(table.split("_")):
        for b in (0, 1):
            s = pair[3*b:3*b+3]
            if s != "---":
                out[q, b] = (int(s[0]), 1 if s[1] == "R" else -1, ord(s[2])-65)
    return out


def T(n):
    return 4*(4**n) + 8*(3**(n-1)) - 7*(2**n) - 1


def rle(bits):
    if not bits:
        return []
    out, cur, count = [], bits[0], 1
    for b in bits[1:]:
        if b == cur:
            count += 1
        else:
            out.append((cur, count))
            cur, count = b, 1
    out.append((cur, count))
    return out


def sides(tape, head):
    if not tape:
        return [], []
    lo, hi = min(tape | {head}), max(tape | {head})
    left = [1 if x in tape else 0 for x in range(head-1, lo-1, -1)]
    right = [1 if x in tape else 0 for x in range(head+1, hi+1)]
    return rle(left), rle(right)


def rho_zero(z):
    if z == 3:
        return 3
    # The reachable family uses signed residues -1,0,1,2 modulo 8.
    choices = [(s, (z-s)//8) for s in (-1, 0, 1, 2)
               if z >= s and (z-s) % 8 == 0 and (z-s)//8 >= 0]
    assert len(choices) == 1, (z, choices)
    s, q = choices[0]
    return 16*q + s


def rho_left(runs):
    return [(b, 2*n if b else rho_zero(n)) for b, n in runs]


def rho_right(runs):
    assert len(runs) >= 3 and len(runs) % 2 == 1
    assert runs[0][0] == 1 and runs[-1][0] == 1
    m = (len(runs)+1)//2
    out = []
    for i, (b, n) in enumerate(runs):
        if b:
            j = i//2 + 1
            if j == 1:
                y = 2*n + 2
            elif j == 2 and m == 2:
                y = 2*n + 4
            elif j == 2:
                y = 2*n + 3
            elif j == m:
                y = 2*n + 1
            else:
                y = 2*n
        else:
            j = (i+1)//2
            y = 2*n - 1 if j <= 2 else 2*n + 1
        out.append((b, y))
    return out


def sigma(c):
    return "ABA" if c == "A" else "BBA"


def main():
    trans = parse(TABLE)
    tape, q, head = set(), 0, 0
    # all A0 returns in each epoch; every third return is a triad boundary.
    returns = {n: [] for n in range(2, MAX_LEVEL+1)}
    final = T(MAX_LEVEL+1)

    for t in range(final+1):
        b = 1 if head in tape else 0
        if q == 0 and b == 0:
            for n in range(2, MAX_LEVEL+1):
                if T(n) <= t <= T(n+1):
                    returns[n].append((t, sides(tape, head)))
                    break
        if t == final:
            break
        mv = trans.get((q, b))
        assert mv is not None, ("undefined F1 queried", t, q, b, head)
        w, d, q = mv
        if w:
            tape.add(head)
        else:
            tape.discard(head)
        head += d

    words = {2: "ABBA"}
    for n in range(3, MAX_LEVEL+1):
        words[n] = "".join(sigma(c) for c in words[n-1])

    boundaries = {}
    for n in range(2, MAX_LEVEL+1):
        rs = returns[n]
        assert (len(rs)-1) % 3 == 0, (n, len(rs))
        bs = [rs[i] for i in range(0, len(rs), 3)]
        assert len(bs) == len(words[n]) + 1, (n, len(bs), len(words[n]))
        boundaries[n] = bs

    checked = 0
    for n in range(2, MAX_LEVEL):
        low = boundaries[n]
        high = boundaries[n+1]
        for k, ((_, (ll, lr))) in enumerate(low):
            _, (hl, hr) = high[3*k]
            assert rho_left(ll) == hl, (n, k, "left", ll, hl, rho_left(ll))
            assert rho_right(lr) == hr, (n, k, "right", lr, hr, rho_right(lr))
            checked += 1
        print(f"rho C_{n}-epoch -> C_{n+1}-epoch: {len(low)} boundaries PASS")

    # Explicitly check the macro-label conjugacy at each lower boundary.
    for n in range(2, MAX_LEVEL):
        low_word, high_word = words[n], words[n+1]
        for k, c in enumerate(low_word):
            assert high_word[3*k:3*k+3] == sigma(c)

    print(f"PASS {checked} exact boundary renormalization checks through level {MAX_LEVEL}")
    print("FINITE EVIDENCE ONLY: prove rho∘A=(ABA)∘rho and rho∘B=(BBA)∘rho on the symbolic domain")


if __name__ == "__main__":
    main()
