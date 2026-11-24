"""Exact finite E/B suffix-graph exploration (not a Lean proof)."""
from collections import Counter
import time,json
RULES=[(1,1,1),(0,1,4),(1,0,2),(0,1,0),(1,0,0),(1,0,3),(1,0,2),(1,0,5),(0,0,2),(0,0,1),(1,0,4),None]
K=12
LIMIT=500

def enc(s):
    return int('1'+s[::-1],2)

def dec(n):
    return bin(n)[3:][::-1]

PAIRS={enc('10'*k):k for k in range(256)}

def efront(s,k0=K):
    l,h,r,q=enc('00'+'10'*k0),0,enc(s[1:]),4
    for t in range(LIMIT+1):
        if q in (1,3) and not h and l in PAIRS:
            k=PAIRS[l]; raw=dec(r);suffix=raw.rstrip('0').lstrip('1'); leading=len(raw)-len(raw.lstrip('1'))
            return ('return',suffix,2*(k-k0)+9+leading,t,k,raw,q)
        if q==5 and h: return ('halt',t)
        rule=RULES[2*q+h]
        if rule is None:raise AssertionError
        w,d,q=rule
        if d:
            l=l*2+w
            if r==1:h=0
            else:h=r&1;r>>=1
        else:
            if l==1:return ('open',t)
            r=r*2+w;h=l&1;l>>=1
    return ('limit',LIMIT)

def bfront(s):
    v=s[1:];return v.rstrip('0').lstrip('1'),9+len(v)-len(v.lstrip('1'))

def bfs(maxdepth=108):
    start=time.time();layer=[{''}];dist={'':0};count={'':1}; unknown=Counter();hals=[]; transitions={}
    for d in range(maxdepth):
        ns=set()
        for s in layer[-1]:
            e=efront(s);transitions[s]=e
            for r,t in ((2,bfront(s)[0]),(1,e[1] if e[0]=='return' else None)):
                if r==1 and e[0]=='halt':hals.append((d,s,r,e));continue
                if t is None:unknown[e[0]]+=1;continue
                if t not in dist:dist[t]=d+1;count[t]=0;ns.add(t)
                if dist[t]==d+1:count[t]+=count[s]
        if (d+1)%10==0 or hals: print('depth',d+1,'layer',len(layer[-1]),'seen',len(dist),'unknown',dict(unknown),'time',round(time.time()-start,3),flush=True)
        if hals: break
        layer.append(ns)
    print('halt',hals,'paths',sum(count[s] for d,s,r,e in hals))
    if not hals:return
    d=hals[0][0];current={s for _,s,_,_ in hals};edges=[]
    for j in range(d-1,-1,-1):
        prev=set()
        for s in layer[j]:
            e=transitions[s]
            for r,t in ((2,bfront(s)[0]),(1,e[1] if e[0]=='return' else None)):
                if t in current:
                    prev.add(s);edges.append((j,s,r,t,e if r==1 else bfront(s)))
        current=prev
    print('DAG states',len(set((d,s) for d,s,r,t,e in edges))+len(hals),'edges',len(edges),'branches',Counter(r for d,s,r,t,e in edges))
    print('E max front time',max(e[3] for d,s,r,t,e in edges if r==1))
    print('E min left pair count',min(e[4] for d,s,r,t,e in edges if r==1))
    print('max suffix length',max(len(s) for d,s,r,t,e in edges))
    for _,s,r,_,e in edges:
        if r==1:
            f=efront(s,3)
            assert f[:4]==e[:4] and f[4]==e[4]-9 and f[5:]==e[5:]
    assert all(efront(s,3)==e for _,s,_,e in hals)
    json.dump({'K':K,'count':sum(count[s] for d,s,r,e in hals),'edges':sorted(edges),'halts':hals},open('route_dag.json','w'),indent=2)
if __name__=='__main__':bfs()
