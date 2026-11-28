#!/usr/bin/env python3
"""Compact a frozen asymmetric NGram witness using partial DFA congruences.

Discovery only: the replacement must pass the original Lean FastBiDFA checker.
Never modify the transition table, namespace, or exported live theorem.
"""
from collections import defaultdict, deque
from pathlib import Path
import re
import sys


def decode(tokens):
    out = set()

    def visit(offset, weight):
        tok = next(tokens)
        if tok == ".leaf":
            out.add(offset)
        elif tok == ".branch":
            visit(offset, weight * 2)
            visit(offset + weight, weight * 2)
        else:
            assert tok == ".empty", tok

    visit(0, 1)
    return out


def load(source):
    m = re.search(r"def cert : Cert := ⟨(\d+),\s*(\d+),\s*(.*?)⟩\n", source, re.S)
    assert m, "expected original NGram certificate"
    nl, nr = map(int, m.groups()[:2])
    wL, wR = 1 << (nl + 1), 1 << (nr + 1)
    tokens = iter(re.findall(r"\.(?:empty|leaf|branch)", m[3]))
    E = []
    for w in (wL, wR):
        E.append({
            (v // 2, (v // 2) % 2, (v // 2) // 2 + (w // 2) * (v % 2))
            for v in decode(tokens)
        })
    S = {(i // 2, i % 2, v // wR, v % wR)
         for i in range(12) for v in decode(tokens)}
    assert next(tokens, None) is None
    trans = {
        (int(q), int(a == "true")): (int(w == "true"), int(d == "true"), int(j))
        for q, a, w, d, j in re.findall(
            r"\| \((\d), (true|false)\) => some \(some ⟨(true|false), (true|false), (\d)⟩\)",
            source
        )
    }
    D = [[(2*x+b) % w for x in range(w) for b in range(2)] for w in (wL,wR)]
    for d, e in zip(D, E):
        assert all(d[2*u+b] == t for t,b,u in e)
    return m, trans, D, E, S


def close(trans, D, cap):
    """Least abstract state/edge fixed point, seeded only by blank."""
    E = [defaultdict(set), defaultdict(set)]
    W = [defaultdict(set), defaultdict(set)]
    for e in E:
        e[0].add((0, 0))
    S = {(0, 0, 0, 0)}
    Q = deque(S)

    def add(z):
        if z not in S:
            S.add(z)
            Q.append(z)

    def move(z, b, u):
        q, a, l, r = z
        w, d, j = trans[q, a]
        add((j,b,D[0][2*l+w],u) if d else (j,b,u,D[1][2*r+w]))

    while Q:
        if len(S) > cap:
            return None
        z = Q.popleft()
        q, a, l, r = z
        if (q, a) not in trans:
            return None
        w, d, j = trans[q, a]
        k = 0 if d else 1
        u = (l, r)[k]
        t = D[k][2*u+w]
        if (w, u) not in E[k][t]:
            E[k][t].add((w, u))
            for zz in W[k][t]:
                move(zz, w, u)
        v = (l, r)[1-k]
        W[1-k][v].add(z)
        for b, u in E[1-k][v]:
            move(z, b, u)
    return [{(t,b,u) for t,es in e.items() for b,u in es} for e in E], S


def stats(D, E, S):
    return len(D[0])//2, len(D[1])//2, len(E[0]), len(E[1]), len(S)


def partial_merge(d, edges, labels, seeds):
    """Require congruence only when both classes have an observed push."""
    n = len(d)//2
    p = list(range(n))
    outgoing = [{} for _ in range(n)]
    for t, b, u in edges:
        assert outgoing[u].setdefault(b, t) == t

    def root(x):
        while p[x] != x:
            x = p[x]
        return x

    todo = list(seeds)
    while todo:
        i, j = map(root, todo.pop())
        if i == j:
            continue
        if labels[i] != labels[j]:
            return None
        if i > j:
            i, j = j, i
        p[j] = i
        for b, t in outgoing[j].items():
            if b in outgoing[i]:
                todo.append((outgoing[i][b], t))
            else:
                outgoing[i][b] = t
    classes = {}
    P = [classes.setdefault(root(i), len(classes)) for i in range(n)]
    assert P[0] == 0
    # A missing observed transition is a don't-care. Map it to blank.
    D = [0]*(2*len(classes))
    for i in range(n):
        if p[i] == i:
            for b, t in outgoing[i].items():
                D[2*P[i]+b] = P[t]
    return D, P


def relation_labels(D, S, k):
    labels = [set() for _ in range(len(D[k])//2)]
    for q, a, l, r in S:
        labels[(l,r)[k]].add((q,a,(l,r)[1-k]))
    return list(map(frozenset, labels))


def exact_quotient(trans, D, E, S):
    """Alternate relation-labelled partial congruences and fresh saturation."""
    while True:
        before = stats(D, E, S)
        for k in (0, 1):
            labels = relation_labels(D,S,k)
            groups = defaultdict(list)
            for i, label in enumerate(labels):
                groups[label].append(i)
            seeds = [(g[0],x) for g in groups.values() for x in g[1:]]
            # Deterministic order independent of input set iteration.
            seeds.sort()
            m = partial_merge(D[k],E[k],labels,seeds)
            if m is None:
                accepted = []
                m = partial_merge(D[k],E[k],labels,[])
                for pair in seeds:
                    if m[1][pair[0]] == m[1][pair[1]]:
                        continue
                    candidate = partial_merge(D[k],E[k],labels,accepted+[pair])
                    if candidate is not None:
                        accepted.append(pair)
                        m = candidate
            DD = D.copy()
            DD[k] = m[0]
            if len(DD[k]) >= len(D[k]):
                continue
            out = close(trans, DD, cap=max(len(S)*2+100,1000))
            if out is None:
                continue
            D = DD
            E, S = out
        after = stats(D, E, S)
        if after == before:
            return D, E, S
        print("quotient", before, "->", after, flush=True)


def trie(xs):
    if not xs:
        return ".empty"
    if xs == {0}:
        return ".leaf"
    return f"(.branch {trie({x//2 for x in xs if x%2==0})} {trie({x//2 for x in xs if x%2})})"


def render(src, m, D, E, S):
    el = [set() for _ in range(len(D[0])//2)]
    er = [set() for _ in range(len(D[1])//2)]
    for e, es in zip((el,er),E):
        for t, b, u in es:
            e[t].add(2*u+b)
    nr = len(D[1])//2
    rows = [set() for _ in range(12)]
    for q, a, l, r in S:
        rows[2*q+a].add(r+nr*l)
    ar = lambda a: "#[" + ", ".join(map(trie,a)) + "]"
    cert = "def cert : FastCert := ⟨" + ", ".join(
        (str(D[0]),str(D[1]),ar(el),ar(er),str(nr),ar(rows))
    ) + "⟩\n"
    src = src[:m.start()] + cert + src[m.end():]
    return src.replace("import AsymNGram","import FastBiDFA").replace(
        "BB6.Agent32AsymNGram","BB6.Agent32FastBiDFA"
    ).replace(":= by decide\n",":= by decide +kernel\n")


def transform(src):
    m,trans,D,E,S = load(src)
    before = stats(D,E,S)
    out = close(trans,D,cap=len(S)+1)
    assert out is not None, "original fixed point not reproduced"
    EE,T = out
    assert T <= S and all(e <= old for e, old in zip(EE,E))
    D,E,S = exact_quotient(trans,D,EE,T)
    return render(src,m,D,E,S),before,stats(D,E,S)


if __name__ == "__main__":
    source = Path(sys.argv[1])
    target = Path(sys.argv[2]) if len(sys.argv) > 2 else source
    out,before,after = transform(source.read_text())
    print(source.name,before,"->",after)
    target.write_text(out)
