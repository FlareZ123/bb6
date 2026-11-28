#!/usr/bin/env python3
"""Reproduce the Raw140 residual-37 block trace and affine middle recurrence."""

TABLE = [7, 21, 11, 12, 15, 1, 6, 18, 4, 17, 17, 24]
TAIL542 = [5, 4, 2]
TAIL_DEEP = [2, 1, 5]

def block_exit(q, direction, word):
    p = 0 if direction else 2
    w = word
    steps = 0
    while 0 <= p < 3:
        bit = (w >> p) & 1
        code = TABLE[2*q + bit]
        if code == 24:
            return None
        write = (code >> 1) & 1
        w = (w & ~(1 << p)) | (write << p)
        q = code >> 2
        p += 1 if code & 1 else -1
        steps += 1
    return q, p >= 3, w, steps

def push(word, xs):
    return xs if word == 0 and not xs else [word] + xs

def advance(state):
    q, direction, left, right = state
    word = (right[0] if right else 0) if direction else (left[0] if left else 0)
    l = left[:] if direction else (left[1:] if left else [])
    r = (right[1:] if right else []) if direction else right[:]
    out = block_exit(q, direction, word)
    assert out is not None
    q2, d2, w2, steps = out
    if d2:
        l = push(w2, l)
    else:
        r = push(w2, r)
    return (q2, d2, l, r), steps

def marks(m):
    return [5, 5, 4] * m

def K(m):
    return (
        4, True,
        [2, 4, 4] + marks(m) + [5] * (67 + 6*m) + [6] * (159 - 6*m) + [4],
        TAIL542,
    )

def transfer_out():
    bank3 = [1, 3, 3] * 3
    return (
        4, True,
        [1] + bank3 + [2, 2, 6, 7] + [3] * 74 + [2],
        [5, 2, 1, 5],
    )

def deep():
    return (1, False, [1, 1] + [3] * 134 + [5] * 410, TAIL_DEEP)

def main():
    state = transfer_out()
    primitive = 0
    macro = 0
    milestones = []
    k_seen = {}

    while state != deep():
        for m in range(27):
            if state == K(m) and m not in k_seen:
                k_seen[m] = (macro, primitive)
                milestones.append(("K", m, macro, primitive))
        state, cost = advance(state)
        primitive += cost
        macro += 1
        assert macro <= 505387

    assert macro == 505387
    assert primitive == 1454281
    for m in range(27):
        assert m in k_seen
    for m in range(26):
        a_macro, a_prim = k_seen[m]
        b_macro, b_prim = k_seen[m+1]
        assert b_macro - a_macro == 3663 + 432*m
        assert b_prim - a_prim == 10075 + 1188*m

    assert k_seen[0] == (80164, 227666)
    assert k_seen[26] == (315802, 875716)
    assert k_seen[26][0] - k_seen[0][0] == 235638
    assert k_seen[26][1] - k_seen[0][1] == 648050

    print("transferOut -> deep:", macro, "block exits,", primitive, "primitive steps")
    print("K0:", k_seen[0], "K26:", k_seen[26])
    print("verified K_m -> K_(m+1) costs for m=0..25")
    for row in milestones:
        print(row)

if __name__ == "__main__":
    main()
