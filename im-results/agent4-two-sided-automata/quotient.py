"""Incidence quotient of finite two-stack relation candidates.

This is an untrusted optimization; Lean independently checks each result.
"""
from collections import defaultdict


def valid(p, cert):
    ok, n, edges, seen, pushes, tab = cert
    if not ok or n != len(seen) or (0, 0, 0, 0) not in seen:
        return False
    if any(not tab[d] or (0, 0) not in edges[d][0] for d in (0, 1)):
        return False
    for q, a, l, r in seen:
        move = p[2*q+a]
        if move in ('---', 'HHH'):
            return False
        w, d, s = int(move[0]), int(move[1]=='L'), ord(move[2])-65
        stacks = [l, r]
        j = pushes[d].get((stacks[d], w), 0)
        if not (0 <= j < len(tab[d])) or (w, stacks[d]) not in edges[d][j]:
            return False
        for b, i in edges[1-d][stacks[1-d]]:
            succ = [0, 0]
            succ[d], succ[1-d] = j, i
            if (s, b, *succ) not in seen:
                return False
    return True


def quotient_side(cert, d):
    ok, _, edges, seen, pushes, tab = cert
    incidence = [set() for _ in tab[d]]
    for q, a, l, r in seen:
        pair = (l, r)
        incidence[pair[d]].add((q, a, pair[1-d]))
    groups = {}
    phi = []
    reps = []
    for i, row in enumerate(incidence):
        key = frozenset(row)
        if key not in groups:
            groups[key] = len(reps)
            reps.append(i)
        phi.append(groups[key])
    if len(reps) == len(phi):
        return cert
    E, D, T = list(edges), list(pushes), list(tab)
    E[d] = defaultdict(set)
    for i in range(len(phi)):
        for b, j in edges[d][i]:
            E[d][phi[i]].add((b, phi[j]))
    D[d] = {}
    for j, i in enumerate(reps):
        for b in (0, 1):
            D[d][j,b] = phi[pushes[d].get((i,b),0)]
    T[d] = [tab[d][i] for i in reps]
    S = {(q,a,phi[l] if d==0 else l,phi[r] if d==1 else r) for q,a,l,r in seen}
    return ok, len(S), E, S, D, T


def compress(p, cert):
    if not valid(p, cert):
        raise ValueError('invalid original certificate')
    while True:
        prev = tuple(map(len, cert[-1]))
        for d in (0, 1):
            cert = quotient_side(cert, d)
            if not valid(p, cert):
                raise AssertionError('quotient does not satisfy closure')
        if tuple(map(len, cert[-1])) == prev:
            return cert
