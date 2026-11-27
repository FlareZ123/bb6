#!/usr/bin/env python3
"""Generate packed relation witnesses from exact BiDFA/asymmetric n-gram sources.

Discovery only: all output is checked by PackedMatrixBiDFA.never in Lean.
The first quotient preserves exact safety labels, then the tape-edge-observed
quotient treats unused push transitions as don't-cares. Optional congruence
merges are accepted only if a new abstract closure succeeds from the blank.
"""
from collections import defaultdict
from pathlib import Path
import re
import sys
from minimize_bidfa import parse, partition
from coarsen_ngram import load, greedy


def partial_side(d,edges,labels,used):
    used = sorted(used | {0})
    trans = {}
    for t,b,u in edges:
        assert d[2*u+b] == t
        assert (u,b) not in trans or trans[u,b] == t
        trans[u,b] = t
    groups = {}
    P = {i:groups.setdefault(frozenset(labels[i]),len(groups)) for i in used}
    while True:
        classes = defaultdict(list)
        for i in used:
            classes[P[i]].append(i)
        blocks = []
        for _,items in sorted(classes.items()):
            G = []
            def sig(i):
                return tuple(P[trans[i,b]] if (i,b) in trans else None for b in range(2))
            for i in sorted(items,key=lambda i:(-sum(x is not None for x in sig(i)),i)):
                t = sig(i)
                for j,(s,members) in enumerate(G):
                    if all(a is None or b is None or a == b for a,b in zip(t,s)):
                        G[j] = (tuple(a if a is not None else b for a,b in zip(t,s)),members+[i])
                        break
                else:
                    G.append((t,[i]))
            blocks.extend(m for s,m in G)
        blocks.sort(key=min)
        Q = {i:k for k,g in enumerate(blocks) for i in g}
        if Q == P:
            break
        P = Q
    assert P[0] == 0
    D = [0]*(2*len(set(P.values())))
    seen = {}
    for (i,b),j in trans.items():
        k,v = 2*P[i]+b,P[j]
        assert k not in seen or seen[k] == v
        seen[k] = v
        D[k] = v
    E = {(P[t],b,P[u]) for t,b,u in edges}
    return D,P,E


def partial_quotient(dl,dr,el,er,S):
    L,R = defaultdict(set),defaultdict(set)
    for q,a,l,r in S:
        L[l].add((q,a,r))
        R[r].add((q,a,l))
    ul = set(L) | {t for t,b,u in el} | {u for t,b,u in el}
    ur = set(R) | {t for t,b,u in er} | {u for t,b,u in er}
    DL,l,EL = partial_side(dl,el,L,ul)
    DR,r,ER = partial_side(dr,er,R,ur)
    T = {(q,a,l[x],r[y]) for q,a,x,y in S}
    return DL,DR,EL,ER,T


def fixed(dl,dr,el,er,S):
    a = (dl,dr,el,er,S)
    while True:
        z = partial_quotient(*a)
        if (len(z[0]),len(z[1]),len(z[4])) == (len(a[0]),len(a[1]),len(a[4])):
            return z
        a = z


def encode(xs,width):
    return hex(sum(x<<(width*i) for i,x in enumerate(xs)))


def packed(s,m,dl,dr,el,er,S):
    nl,nr = len(dl)//2,len(dr)//2
    wl,wr = max(1,(nl-1).bit_length()),max(1,(nr-1).bit_length())
    EL,ER,R = [0]*(2*nl),[0]*(2*nr),[0]*(12*nl)
    for t,b,u in el:
        EL[2*t+b] |= 1<<u
    for t,b,u in er:
        ER[2*t+b] |= 1<<u
    for q,a,l,r in S:
        R[(2*q+a)*nl+l] |= 1<<r
    cert = f'def cert : MatrixCert := ⟨⟨{wl},{encode(dl,wl)}⟩,⟨{wr},{encode(dr,wr)}⟩,{nl},{nr},{encode(EL,nl)},{encode(ER,nr)},{encode(R,nr)}⟩\n'
    out = s[:m.start()]+cert+s[m.end():].lstrip("\n")
    out = out.replace("import AsymNGram","import PackedMatrixBiDFA").replace("import BiDFA","import PackedMatrixBiDFA")
    out = out.replace("open BB6Coverage BB6.Agent32AsymNGram","open BB6Coverage BB6.Agent32PackedMatrixBiDFA")
    out = out.replace("open BB6Coverage BB6Coverage.Agent16BiDFA","open BB6Coverage BB6.Agent32PackedMatrixBiDFA")
    return out.replace(":= by decide\n",":= by decide +kernel\n")


def transform(s, round_limit=27):
    if "import AsymNGram" in s:
        m,trans,dl,dr,el,er,S,before = load(s)
    elif "import BiDFA" in s:
        m,dl,dr,el,er,S = parse(s)
        before = (len(dl)//2,len(dr)//2,len(S))
        trans = {(int(q),int(a=="true")):(int(w=="true"),int(d=="true"),int(j))
                 for q,a,w,d,j in re.findall(
                     r'\| \((\d), (true|false)\) => some \(some ⟨(true|false), (true|false), (\d)⟩\)', s)}
    else:
        raise ValueError("expected original generated list or asymmetric n-gram certificate")
    dl,dr,el,er,S = fixed(dl,dr,el,er,S)
    if round_limit and max(len(dl),len(dr))>300 and len(S)>1500:
        dl,dr,el,er,S = greedy(trans,dl,dr,el,er,S,round_limit)
    return packed(s,m,dl,dr,el,er,S),before,(len(dl)//2,len(dr)//2,len(S))


if __name__ == "__main__":
    p = Path(sys.argv[1])
    out,before,after = transform(p.read_text(), int(sys.argv[2]) if len(sys.argv)>2 else 27)
    print(p.name,before,"->",after)
    p.write_text(out)
