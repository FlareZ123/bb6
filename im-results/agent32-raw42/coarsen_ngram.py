#!/usr/bin/env python3
"""Untrusted discovery: compress asymmetric n-gram witnesses as BiDFAs.

The original source-machine theorem is accepted only after the resulting
FastBiDFA certificate is checked in Lean. Congruence merges need not preserve
the original relation: each candidate gets a fresh inductive closure from
the blank configuration, with the projected old edges as a conservative seed.
"""
from collections import defaultdict, deque
from itertools import combinations
import re
import sys
from pathlib import Path
from minimize_bidfa import partition, literal_rows
from convert_bidfa import convert


def decode(tokens):
    tok = next(tokens)
    if tok == ".empty":
        return set()
    if tok == ".leaf":
        return {0}
    assert tok == ".branch", tok
    even, odd = decode(tokens), decode(tokens)
    return {2*x for x in even} | {2*x+1 for x in odd}


def side(n, es):
    mod = 2**n
    d = [b+2*(x % mod) for x in range(2*mod) for b in range(2)]
    # Edge index 2*window+extension, window's low bit is popped.
    edges = [(v//2, (v//2)%2, (v//2)//2+mod*(v%2)) for v in es]
    assert all(d[2*s+b] == t for t,b,s in edges)
    return d, edges


def load(s):
    m = re.search(r'def cert : Cert := ⟨(\d+),\s*(\d+),\s*(.*?)⟩\n', s, re.S)
    assert m
    nl, nr = map(int, m.groups()[:2])
    ts = iter(re.findall(r'\.(?:empty|leaf|branch)', m[3]))
    el, er = decode(ts), decode(ts)
    rows = [decode(ts) for _ in range(12)]
    assert next(ts, None) is None
    dl, el = side(nl, el)
    dr, er = side(nr, er)
    width = 2**(nr+1)
    S = {(i//2,i%2,v//width,v%width) for i,row in enumerate(rows) for v in row}
    trans = {(int(q),int(a=="true")):(int(w=="true"),int(d=="true"),int(j))
             for q,a,w,d,j in re.findall(
                 r'\| \((\d), (true|false)\) => some \(some ⟨(true|false), (true|false), (\d)⟩\)', s)}
    left = [set() for _ in range(len(dl)//2)]
    right = [set() for _ in range(len(dr)//2)]
    for q,a,l,r in S:
        left[l].add((q,a,r))
        right[r].add((q,a,l))
    DL,L = partition(dl, list(map(frozenset,left)))
    DR,R = partition(dr, list(map(frozenset,right)))
    EL = {(L[t],b,L[u]) for t,b,u in el}
    ER = {(R[t],b,R[u]) for t,b,u in er}
    T = {(q,a,L[l],R[r]) for q,a,l,r in S}
    return m, trans, DL, DR, EL, ER, T, (len(dl)//2,len(dr)//2,len(S))


def merge(d, i, j):
    n = len(d)//2
    p = list(range(n))
    todo = [(i,j)]
    def root(a):
        while p[a] != a:
            a = p[a]
        return a
    while todo:
        a,b = map(root,todo.pop())
        if a == b:
            continue
        if a > b:
            a,b = b,a
        p[b] = a
        todo.extend((d[2*a+k],d[2*b+k]) for k in range(2))
    cls = {}
    P = [cls.setdefault(root(k),len(cls)) for k in range(n)]
    D = [0]*(2*len(cls))
    for k in range(n):
        D[2*P[k]:2*P[k]+2] = [P[d[2*k]],P[d[2*k+1]]]
    assert P[0] == 0
    return D,P


def close(trans,dl,dr,el,er,cap):
    E = [defaultdict(set),defaultdict(set)]
    watch = [defaultdict(set),defaultdict(set)]
    for i,ee in enumerate((el,er)):
        for t,b,u in ee:
            E[i][t].add((b,u))
    assert (0,0) in E[0][0] and (0,0) in E[1][0]
    S = {(0,0,0,0)}
    Q = deque(S)
    def add(z):
        if z not in S:
            S.add(z)
            Q.append(z)
    def step(z,b,u):
        q,a,l,r = z
        w,d,j = trans[q,a]
        if d:
            add((j,b,dl[2*l+w],u))
        else:
            add((j,b,u,dr[2*r+w]))
    while Q:
        if len(S) > cap:
            return None
        z = Q.popleft()
        q,a,l,r = z
        if (q,a) not in trans:
            return None
        w,d,j = trans[q,a]
        k = 0 if d else 1
        t = dl[2*l+w] if d else dr[2*r+w]
        u = l if d else r
        if (w,u) not in E[k][t]:
            E[k][t].add((w,u))
            for zz in watch[k][t]:
                step(zz,w,u)
        v = r if d else l
        watch[1-k][v].add(z)
        for b,u in E[1-k][v]:
            step(z,b,u)
    el,er = ({(t,b,u) for t,ee in e.items() for b,u in ee} for e in E)
    return el,er,S


def greedy(trans,dl,dr,el,er,S,round_limit=27):
    for _ in range(round_limit):
        ls = [set() for _ in range(len(dl)//2)]
        rs = [set() for _ in range(len(dr)//2)]
        for q,a,l,r in S:
            ls[l].add((q,a,r))
            rs[r].add((q,a,l))
        pairs = []
        for side,labels in enumerate((ls,rs)):
            for i,j in combinations(range(len(labels)),2):
                x,y = labels[i],labels[j]
                score = len(x^y)/(len(x|y) or 1)
                pairs.append((score,len(x^y),side,i,j))
        pairs.sort()
        found = False
        for _,__,k,i,j in pairs:
            if k == 0:
                DL,L = merge(dl,i,j)
                DR,R = dr,list(range(len(dr)//2))
            else:
                DR,R = merge(dr,i,j)
                DL,L = dl,list(range(len(dl)//2))
            EL = {(L[t],b,L[u]) for t,b,u in el}
            ER = {(R[t],b,R[u]) for t,b,u in er}
            result = close(trans,DL,DR,EL,ER,max(500,len(S)+50))
            if result is None:
                continue
            E1,E2,T = result
            if len(T) > len(S)+30:
                continue
            dl,dr,el,er,S = DL,DR,E1,E2,T
            found = True
            break
        if not found:
            break
    return dl,dr,el,er,S


def transform(s,round_limit=27):
    m,trans,dl,dr,el,er,S,before = load(s)
    dl,dr,el,er,S = greedy(trans,dl,dr,el,er,S,round_limit)
    cert = "def cert : Cert := ⟨" + ",".join((
        str(dl),str(dr),literal_rows(sorted(el)),literal_rows(sorted(er)),
        literal_rows(sorted(S)))) + "⟩\n"
    s = s[:m.start()] + cert + s[m.end():]
    s = convert(s.replace("import AsymNGram","import BiDFA").replace(
        "open BB6Coverage BB6.Agent32AsymNGram",
        "open BB6Coverage BB6Coverage.Agent16BiDFA"))
    return s.replace(":= by decide\n",":= by decide +kernel\n"),before,(len(dl)//2,len(dr)//2,len(S))


if __name__ == "__main__":
    p = Path(sys.argv[1])
    out,before,after = transform(p.read_text(), int(sys.argv[2]) if len(sys.argv)>2 else 27)
    print(p.name,before,"->",after)
    p.write_text(out)
