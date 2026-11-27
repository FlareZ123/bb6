"""Raw39/1LE 180: exact sweep preimages (Python 3, no dependencies).
No assertion of unbounded nonhalting unless an inductive invariant is found.
"""
from collections import deque
from functools import lru_cache
import sys

# Alphabet 0,1,2=#, -1=epsilon.
RULES = [('0000','1011',2,6),('0001','1100',4,4),
 ('00100','10111',2,10),('00101','11000',5,7),
 ('00110','11011',3,11),('00111','11100',5,9),
 ('01000','10111',2,8),('01001','11000',5,5),
 ('01010','11011',3,9),('01011','11100',5,7)]
TABLE = [(1,1,1),(1,-1,4),(1,1,2),(1,1,5),(0,1,3),(0,-1,1),
         (1,-1,3),(0,1,0),(0,-1,0),(0,-1,4),(0,1,2),None]

def check_rules():
    prefixes = [u for u,v,h,t in RULES]+['011']
    assert all(sum(w.startswith(u) for u in prefixes)==1
               for w in (format(i,'05b') for i in range(16)))
    for u,v,h,t in RULES:
        a=list(map(int,u));q=i=0
        for j in range(t):
            assert 0<=i<len(a)
            w,d,q=TABLE[2*q+a[i]];a[i]=w;i+=d
            assert q!=0 or j==t-1
        assert q==0 and i==h and ''.join(map(str,a))==v
    q=i=0;a=[0,1,1]
    for _ in range(2):
        w,d,q=TABLE[2*q+a[i]];a[i]=w;i+=d
    assert TABLE[2*q+a[i]] is None

class Trans:
    def __init__(self,e,start,final):
        self.e=e;self.start=start;self.final=set(final)
    def inverse(self):
        return Trans([[(o,i,u) for i,o,u in row] for row in self.e],
                     self.start,self.final)

def right():
    e=[[(0,0,0),(1,1,0),(2,-1,1)],[(-1,2,2)],[(0,0,2),(1,1,2)]]
    for u,v,h,t in RULES:
        pairs=list(zip(map(int,u),map(int,v)))
        if h<len(v):pairs.insert(h,(-1,2))
        cur=1
        for j,(i,o) in enumerate(pairs):
            if j==len(pairs)-1:nxt=1 if h==len(v) else 2
            else:nxt=len(e);e.append([])
            e[cur].append((i,o,nxt));cur=nxt
    return Trans(e,0,{2})

def left():
    return Trans([[(0,0,0),(1,1,0),(2,2,6),(-1,2,1)],
      [(0,0,2),(1,1,2)],[(0,0,3)],
      [(1,0,3),(1,1,4),(2,-1,5)],[(0,0,3)],
      [(1,1,6)],[(0,0,6),(1,1,6)]],0,{6})

def minimize(D):
    d,s,f=D;n=len(d);p=[int(i in f) for i in range(n)]
    while True:
        mp={};q=[]
        for i in range(n):
            key=(p[i],*(p[j] for j in d[i]))
            if key not in mp:mp[key]=len(mp)
            q.append(mp[key])
        if len(mp)==len(set(p)):break
        p=q
    ds=[None]*len(mp);fs=set()
    for i in range(n):
        ds[q[i]]=tuple(q[j] for j in d[i])
        if i in f:fs.add(q[i])
    st=q[s];ids={st:0};todo=deque([st]);dt=[];ft=set()
    while todo:
        v=todo.popleft()
        if v in fs:ft.add(ids[v])
        vv=[]
        for j in ds[v]:
            if j not in ids:ids[j]=len(ids);todo.append(j)
            vv.append(ids[j])
        dt.append(tuple(vv))
    return dt,0,ft

def preimage(T,D,cap=200000):
    d,s,f=D;N=len(d)
    @lru_cache(None)
    def ec(x):
        seen={x};todo=[x]
        for p in todo:
            t,k=divmod(p,N)
            for i,o,u in T.e[t]:
                if i!=-1:continue
                q=u*N+(k if o==-1 else d[k][o])
                if q not in seen:seen.add(q);todo.append(q)
        return frozenset(seen)
    @lru_cache(None)
    def move(x,b):
        t,k=divmod(x,N);res=set()
        for i,o,u in T.e[t]:
            if i==b:res.update(ec(u*N+(k if o==-1 else d[k][o])))
        return frozenset(res)
    start=ec(T.start*N+s);ids={start:0};todo=deque([start]);dt=[];ft=set()
    while todo:
        v=todo.popleft()
        if any(t in T.final and k in f for t,k in (divmod(x,N) for x in v)):
            ft.add(ids[v])
        row=[]
        for b in range(3):
            w=frozenset(y for x in v for y in move(x,b))
            if w not in ids:
                if len(ids)>=cap:raise OverflowError(cap)
                ids[w]=len(ids);todo.append(w)
            row.append(ids[w])
        dt.append(tuple(row))
    return minimize((dt,0,ft))

def intersection_nonempty(D,E):
    d,s,f=D;e,t,g=E;seen={(s,t)};todo=deque([(s,t)])
    while todo:
        i,j=todo.popleft()
        if i in f and j in g:return True
        for b in range(3):
            z=d[i][b],e[j][b]
            if z not in seen:seen.add(z);todo.append(z)
    return False

def included(D,E):
    e,t,g=E
    return not intersection_nonempty(D,(e,t,set(range(len(e)))-g))

BAD=([(0,0,1),(2,3,3),(3,4,3),(3,3,3),(3,5,3),(5,5,3)],0,{5})
BLANK=([(0,1,2),(1,1,1),(2,1,1)],0,{2})

def certificate(K):
    R,L=right(),left()
    return (included(BLANK,K) and not intersection_nonempty(BAD,K)
            and included(preimage(R.inverse(),K),K)
            and included(preimage(L.inverse(),K),K))

if __name__=='__main__':
    check_rules()
    R,L=right(),left();D=BAD
    for i in range(int(sys.argv[1]) if len(sys.argv)>1 else 12):
        D=preimage((R,L)[i%2],D)
        assert not intersection_nonempty(D,BLANK)
        print(i+1,len(D[0]),flush=True)
