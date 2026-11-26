"""Convert a sparse exact n-gram closure to the existing two-stack relation.
Untrusted conversion: valid/compress and Lean's checked certificate validate closure.
The initial blank window 0 keeps index 0 on both sides.
"""
from collections import defaultdict

def from_sparse(p,data):
    k,n,L,R,S=data.split()
    k,n=int(k),int(n)
    M=1<<k
    mask=M-1
    rows=[]
    for j in map(int,S.rstrip(',').split(',')):
        r=j&mask
        j>>=k
        l=j&mask
        s=j>>k
        rows.append((s//2,s%2,l,r))
    assert len(set(rows))==n
    T,ids,E,D=[],[],[],[]
    for d,encoded in enumerate((L,R)):
        states={0}|{x[2+d] for x in rows}
        raw=[]
        for pair in encoded.rstrip(',').split(','):
            x,v=map(int,pair.split(':'))
            states.add(x)
            for b in (0,1):
                if v&(1<<b):
                    y=(x>>1)|(b<<(k-1))
                    states.add(y)
                    raw.append((x,x&1,y))
        tab=sorted(states)
        index={x:i for i,x in enumerate(tab)}
        ed=defaultdict(set)
        push={}
        for x,b,y in raw:
            ed[index[x]].add((b,index[y]))
            push[index[y],b]=index[x]
        T.append(tab)
        ids.append(index)
        E.append(ed)
        D.append(push)
    seen={(q,a,ids[0][l],ids[1][r]) for q,a,l,r in rows}
    return True,n,E,seen,D,T
