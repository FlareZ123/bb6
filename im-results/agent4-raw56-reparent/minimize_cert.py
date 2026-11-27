"""Untrusted quotient optimization of finite-stack certificates.

Merge stack states with identical reachable-configuration profiles. In the
joint relation, each equivalence class product is saturated, so projected
inverse-pop edges remain safe under any projected, defined representative push.
The original Lean checker independently checks all output.
"""
from collections import defaultdict

def quotient(cert):
    ok,n,E,S,D,T=cert
    assert ok
    while True:
        profiles=[[set() for _ in t] for t in T]
        for q,a,l,r in S:
            profiles[0][l].add((q,a,r));profiles[1][r].add((q,a,l))
        maps=[];tabs=[]
        for d,prof in enumerate(profiles):
            groups={};mp=[];tab=[]
            for i,p in enumerate(prof):
                f=frozenset(p)
                if f not in groups:groups[f]=len(tab);tab.append(T[d][i])
                mp.append(groups[f])
            maps.append(mp);tabs.append(tab)
        if all(len(t)==len(u) for t,u in zip(T,tabs)):break
        es=[defaultdict(set),defaultdict(set)];ds=[{},{}]
        for d,mp in enumerate(maps):
            for i,ls in E[d].items():
                for b,j in ls:es[d][mp[i]].add((b,mp[j]))
            for (i,b),j in D[d].items():ds[d].setdefault((mp[i],b),mp[j])
        S={(q,a,maps[0][l],maps[1][r]) for q,a,l,r in S};E,D,T=es,ds,tabs
    return True,len(S),E,S,D,T

def validate(p,cert):
    ok,n,E,S,D,T=cert
    assert (0,0,0,0) in S and all((0,0) in E[d][0] for d in (0,1))
    for q,a,l,r in S:
        m=p[2*q+a];assert m!='---';w=int(m[0]);s=ord(m[2])-65;d=int(m[1]=='L')
        i,j=(l,r) if d==0 else (r,l);x=D[d][i,w];assert (w,i) in E[d][x]
        for b,k in E[1-d][j]:assert ((s,b,x,k) if d==0 else (s,b,k,x)) in S
