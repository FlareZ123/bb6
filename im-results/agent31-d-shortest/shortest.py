"""Exact E/B shortest-distance and all-A edge audit for Cryptid D.
Suffix integers are little endian, with the canonical delimiter at bit zero.
Independent integer implementation of agent3's total guarded evaluator.
"""
from functools import lru_cache
from collections import Counter

RULES=((1,1,1),(0,1,4),(1,-1,2),(0,1,0),(1,-1,0),(1,-1,3),
       (1,-1,2),(1,-1,5),(0,-1,2),(0,-1,1),(1,-1,4),None)

def canon(w):
    l=0
    while w&1:
        w>>=1
        l+=1
    return l,w

@lru_cache(maxsize=250000)
def first_exit(q,w):
    left=[]
    while True:
        b,z=w&1,w>>1
        ins=RULES[2*q+b]
        if ins is None:
            return None
        b,d,q=ins
        if d==1:
            left.append(b)
            w=z
        else:
            y=b+2*z
            if not left:
                return q,y
            w=left.pop()+2*y

@lru_cache(maxsize=250000)
def e_step(w):
    q=4
    guard=(0,0,1,0,1,0,1,0)
    for p in range(len(guard)+1):
        if p>=2 and p%2==0 and q in (1,3) and not w&1:
            l,s=canon(w>>1)
            return 11-p+l,s
        if q==5 and w&1:
            return None
        assert p<len(guard),(w,q)
        a=first_exit(q,w)
        if a is None:
            return None
        q,y=a
        w=guard[p]+2*y

def step(w,r):
    assert not w&1
    if r==2:
        l,s=canon(w>>1)
        return 9+l,s
    if r==1:
        return e_step(w)
    assert r==0
    v=w>>1
    c=0
    while v&1:
        if v&3==1:
            v>>=2
            c+=2
        elif v&7==7:
            v>>=3
            c+=8
        else:
            ans=e_step((v>>3)<<1)
            return None if ans is None else (ans[0]+c+2,ans[1])
    l,s=canon(v>>1)
    return 11+c+l,s

def a_via_eb(w):
    """Suffix only: replace an A by a sequence of B's and optional E."""
    while w:
        m,z=canon(w>>1)
        if m%3==0:
            return canon(z>>1)[1]
        if m%3==2:
            ans=e_step(z)
            return None if ans is None else ans[1]
        w=z
    return 0

def main():
    D={0:0}
    W={0:1}
    F=[0]
    terminals=[]
    for k in range(1,109):
        nxt=[]
        for s in F:
            for r in (1,2):
                a=step(s,r)
                if a is None:
                    terminals.append((k,s,r))
                    continue
                _,t=a
                if t not in D:
                    D[t]=k
                    W[t]=0
                    nxt.append(t)
                if D[t]==k:
                    W[t]+=W[s]
        assert bool(terminals)==(k==108)
        F=nxt
    assert len(D)==245366
    assert terminals==[(108,218,1)]
    assert sum(W[s] for _,s,_ in terminals)==1057916215296
    gains=Counter()
    for s,k in D.items():
        if k>=108:
            continue
        a=step(s,0)
        assert a is not None
        _,t=a
        assert t==a_via_eb(s)
        assert t in D and D[t]<=k
        gains[D[t]-k]+=1
    assert sum(gains.values())==235046
    assert (min(gains),max(gains))==(-107,0)
    print('EB states',len(D),'terminal',terminals,'shortest words',W[218])
    print('A edges audited',sum(gains.values()),'EB distance change',min(gains),max(gains))

if __name__=='__main__':
    main()
