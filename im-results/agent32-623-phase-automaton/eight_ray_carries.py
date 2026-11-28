#!/usr/bin/env python3
"""Exact joint carry reachability for the eight primitive signed ray forms.

No root trace is used. Reachability here means arbitrary base-three digit pairs
from one of the specified sector offsets, not actual #623 root reachability.
"""
from collections import deque
from itertools import product

RAYS=((1,121),(40,43),(13,61),(16,55),(4,79),(25,37),(7,64),(19,40))
FORMS=tuple((p,(4*p-q)//3) for p,q in RAYS)
assert all(3*b==4*p-q for (p,q),(_,b) in zip(RAYS,FORMS))
DIGITS=tuple(product(range(3),repeat=2))

def step(c,x,y):
    return tuple((a*x+b*y+t)//3 for (a,b),t in zip(FORMS,c))

def closure(gammas):
    starts=[tuple(p*g for p,b in FORMS) for g in gammas]
    ids={z:i for i,z in enumerate(starts)}
    q=deque(starts)
    rows=[]
    while q:
        c=q.popleft()
        row=[]
        for x,y in DIGITS:
            d=step(c,x,y)
            if d not in ids:
                ids[d]=len(ids)
                q.append(d)
            row.append(ids[d])
        rows.append(row)
    assert len(rows)==len(ids)
    return ids,rows

def exact_depth(gamma):
    S={tuple(p*gamma for p,b in FORMS)}
    seen=set()
    n=0
    while frozenset(S) not in seen:
        seen.add(frozenset(S))
        T={step(c,x,y) for c in S for x,y in DIGITS}
        n+=1
        print("depth",gamma,n,len(T))
        if S==T:
            return T,n
        S=T
    raise AssertionError("unexpected nontrivial cycle")

def safe_block(X,Y,d,initial_carries):
    """True iff all eight forms avoid 0 and d-1 for every supplied carry.
    X,Y are the least-significant-first word values, 0 <= X,Y < d=3^length.
    Exact per-coordinate projections suffice for this universal test.
    """
    for i,(a,b) in enumerate(FORMS):
        residues={(a*X+b*Y+c[i])%d for c in initial_carries}
        if 0 in residues or d-1 in residues:
            return False
    return True

if __name__=="__main__":
    for gs in [(0,),(0,2,4,10,18)]:
        ids,rows=closure(gs)
        print("joint closure",gs,len(ids),"states",sum(map(len,rows)),"edges")
    for g in [0,2,4,10,18]:
        S,n=exact_depth(g)
        print("stabilized",g,n,len(S),"ranges",
              [(min(c[i] for c in S),max(c[i] for c in S)) for i in range(8)])
