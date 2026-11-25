"""Reproduce the finite token-stack closure certificate for Raw118 M2869.

Discovery only; the independent Lean Data/Cert/Macro/consumer modules are the
proof. The arrays printed here have invalid sentinel 0, empty-stack state 1.
"""
from collections import deque, defaultdict
import json


def autom(initial, alphabet, push):
    ids, states = {initial: 0}, [initial]
    edges, rev = [], defaultdict(list)
    for state in states:
        row = {}
        for a in alphabet:
            target = push(state, a)
            if target is None:
                continue
            if target not in ids:
                ids[target] = len(states)
                states.append(target)
            j = ids[target]
            row[a] = j
            rev[j, a].append(ids[state])
        edges.append(row)
    return states, edges, rev


def left_push(s, a):
    p, top, sparity, event = s
    if a == 'a' and p == 0: pp = 1
    elif a == 'b' and p == 1: pp = 0
    elif a == 'c' and p == 0 and top == 'b': pp = 0
    elif a == 'd' and p == 1 and top == 'a': pp = 1
    elif a == 'e' and p == 1: pp = 1
    elif a == 's' and p == 0: pp = 1
    else: return None
    return pp, a, sparity ^ (a == 's'), a if a in 'ds' else event


def right_push(s, a):
    top, end, xparity, e0, e1 = s
    if a in 'UV':
        if top: return None
        end = a
    elif top in ('Y', 'U') and a != 'X':
        return None
    if a == 'X':
        e0, e1 = e1, e0
        xparity ^= 1
    elif a == 'Y': e1 = 'y'
    elif a == 'Z': e0 = 'z'
    return a, end, xparity, e0, e1


def discover():
    L, LE, LR = autom((0, '', 0, ''), 'abcdes', left_push)
    R, RE, RR = autom(('', 'E', 0, '', ''), 'XYZUV', right_push)
    roots = [(0, 0, r) for r, s in enumerate(R)
             if s[0] not in ('Y', 'U') and s[1] != 'U'
             and s[2] == int(s[1] == 'V')]
    seen, queue = set(roots), deque(roots)

    def push(edges, i, word):
        for a in reversed(word):
            i = edges[i][a]
        return i

    def add(d, l, r):
        c = (d, l, r)
        if c not in seen:
            seen.add(c)
            queue.append(c)

    while queue:
        direction, l, r = queue.popleft()
        p, b, _, _ = L[l]
        a, end, *_ = R[r]
        if direction == 0:
            if a == '':
                add(1, l, push(RE, 0, 'X' if p == 0 else 'V'))
            elif a == 'X':
                for t in RR[r, 'X']:
                    add(0, push(LE, l, 'a' if p == 0 else 'b'), t)
            elif a == 'Y':
                assert b == ('b' if p == 0 else 'a')
                for t in RR[r, 'Y']:
                    add(0, push(LE, l, 'c' if p == 0 else 'd'), t)
            elif a == 'Z':
                for t in RR[r, 'Z']:
                    if p == 0:
                        add(1, l, push(RE, t, 'XY'))
                    else:
                        add(0, push(LE, l, 'e'), t)
            elif a == 'V':
                add(1, l, push(RE, 0, 'XU' if p == 0 else 'Z'))
            elif a == 'U':
                assert p == 1 and b == 'a'
                for u in LR[l, 'a']:
                    add(0, push(LE, u, 's'), 0)
        else:
            if b == '':
                assert p == 0 and end != 'U'
                add(0, 0, push(RE, r, 'X'))
            elif b in 'ab':
                for u in LR[l, b]:
                    add(1, u, push(RE, r, 'X'))
            elif b == 'c':
                for u in LR[l, b]:
                    add(1, u, push(RE, r, 'Y'))
            elif b in 'es':
                for u in LR[l, b]:
                    add(1, u, push(RE, r, 'Z'))
            elif b == 'd':
                for u in LR[l, 'd']:
                    for v in LR[u, 'a']:
                        add(0, push(LE, v, 's'), r)
    assert (len(L), len(R), len(seen)) == (25, 93, 1181)
    assert (0, 0, RE[0]['Z']) in seen
    left = [0] * 6 + [LE[l].get(a, -1) + 1 for l in range(len(L)) for a in 'abcdes']
    right = [0] * 5 + [RE[r].get(a, -1) + 1 for r in range(len(R)) for a in 'XYZUV']
    phase = [False] + [bool(s[0]) for s in L]
    top = [0] + [0 if not s[1] else 'abcdes'.index(s[1]) + 1 for s in L]
    masks = [0] * (2 * (len(L) + 1))
    for d, l, r in seen:
        masks[2 * (l + 1) + d] |= 1 << (r + 1)
    return dict(leftTable=left, rightTable=right, leftPhaseTable=phase,
                leftTopTable=top, masks=masks)


if __name__ == '__main__':
    print(json.dumps(discover(), indent=2))
