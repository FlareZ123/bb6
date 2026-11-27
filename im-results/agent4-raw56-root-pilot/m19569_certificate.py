"""Finite run-stack invariant for Raw56 E1=1LC M19569.
Python 3, standard library only. Discovery uses macro formulas; verification
uses only the exact primitive table, finite graph and framed replay.
"""
from collections import defaultdict, deque
from functools import lru_cache
import json
TABLE = '1RB0LE_1RC---_0RD1RA_1LD1LE_1RF1LC_0RD0RA'
raw = TABLE.replace('_','')
P = [None if raw[i:i+3]=='---' else
     (int(raw[i]),raw[i+1]=='R',ord(raw[i+2])-65)
     for i in range(0,36,3)]
BASE=256
def pair(b,c): return BASE*b+c
def unpair(x): return divmod(x,BASE)

def macro(lp,rp):
    L,R=deque(lp),deque(map(unpair,rp))
    a=L[0]
    b,c=R[0] if R else (4,0)
    blank=not R
    assert b>0 and (b!=1 or c>=2)
    if b==1:
        L[0]+=1; cost=15
        if c==2:
            R.popleft()
            if R:
                d,e=R[0]; R[0]=(d+2,e)
        else: R[0]=(2,c-2)
    elif b in (2,3):
        R.popleft()
        if R:
            d,e=R[0]; R[0]=(d-1,e)
        if c%2:
            if b==2: L.appendleft(c+2); cost=3*c+3
            else: L[0]+=c+4; cost=3*c+20
            assert not R or R[0][0]>0
        else:
            if b==2: L[0]+=1; cost=6*c+11; gap=c-1
            else:
                L.popleft()
                if L: L[0]+=1
                else: L.append(1)
                cost=3*a+6*c+34; gap=a+c+1
            if R and R[0][0]==0:
                _,e=R.popleft(); R.appendleft((gap,3+e))
            else: R.appendleft((gap,3))
    else:
        L.popleft()
        if L: L[0]+=1
        else: L.append(1)
        cost=3*a+34
        if blank: R.appendleft((a+1,3))
        elif b==4: R[0]=(a+1,c+3)
        else: R[0]=(b-4,c); R.appendleft((a+1,3))
    return cost,tuple(L),tuple(pair(b,c) for b,c in R)

def discover():
    # Inverse edges: summary -> (pushed symbol, previous summary).
    n=(2,3)
    rev=[defaultdict(set),defaultdict(set)]
    wait=[defaultdict(set),defaultdict(set)]
    for d in range(2): rev[d][()].add((0,()))
    seen=set(); todo=deque()
    def add(c,l,r):
        k=(c,l,r)
        if k not in seen:
            seen.add(k);todo.append(k)
            assert len(seen)<1000000
    def resume(d,w,e):
        c,other=w;x,s=e
        l,r=(s,other) if d==0 else (other,s)
        add((*c,x),l,r)
    def push(d,x,l,r,c):
        assert 1<=x<=80 if d==0 else all(1<=v<=80 for v in unpair(x))
        s=l if d==0 else r;t=(x,*s[:n[d]-1]);e=(x,s)
        if e not in rev[d][t]:
            rev[d][t].add(e)
            for w in tuple(wait[d][t]):resume(d,w,e)
        add(c,t,r) if d==0 else add(c,l,t)
    def pop(d,c,l,r):
        s=l if d==0 else r;other=r if d==0 else l;w=(c,other)
        if w in wait[d][s]:return
        wait[d][s].add(w)
        for e in tuple(rev[d][s]):resume(d,w,e)
    push(0,1,(),(),('init',))
    while todo:
        c,l,r=todo.popleft();tag=c[0]
        if tag=='init':push(1,pair(1,3),l,r,('start',))
        elif tag=='start':pop(0,('a',),l,r)
        elif tag=='a':
            a=c[1];assert a>0
            pop(1,('b',a),l,r)
        elif tag=='b':
            a,x=c[1:];b,k=unpair(x)
            if x==0:pop(0,('popL',pair(a+1,3),0),l,r)
            elif b==1:
                assert k>=2
                if k==2:pop(1,('dec',a+1,0,2),l,r)
                else:push(0,a+1,l,r,('pushR',pair(2,k-2)))
            elif b==2:
                if k%2:push(0,a,l,r,('decPopR',k+2,0,-1))
                else:pop(1,('dec',a+1,pair(k-1,3),-1),l,r)
            elif b==3:
                if k%2:pop(1,('dec',a+k+4,0,-1),l,r)
                else:pop(0,('popLDec',pair(a+k+1,3)),l,r)
            elif b==4:pop(0,('popL',pair(a+1,k+3),0),l,r)
            else:pop(0,('popL',pair(a+1,3),pair(b-4,k)),l,r)
        elif tag=='pushR':push(1,c[1],l,r,('start',))
        elif tag=='popL':
            out,tail,h=c[1:];push(0,h+1,l,r,('outR',out,tail))
        elif tag=='outR':
            out,tail=c[1:]
            if tail:push(1,tail,l,r,('pushR',out))
            else:push(1,out,l,r,('start',))
        elif tag=='popLDec':
            out,h=c[1:];pop(1,('dec',h+1,out,-1),l,r)
        elif tag=='decPopR':pop(1,('dec',*c[1:]),l,r)
        elif tag=='dec':
            a,out,offset,x=c[1:];b,k=unpair(x)
            if not x:tail=0
            else:
                b+=offset
                if b==0:
                    assert out
                    ob,ok=unpair(out);out=pair(ob,ok+k);tail=0
                else:tail=pair(b,k)
            if out:push(0,a,l,r,('outR',out,tail))
            elif tail:push(0,a,l,r,('pushR',tail))
            else:push(0,a,l,r,('start',))
        else:raise ValueError(c)
    starts=sorted((l,r) for c,l,r in seen if c==('start',))
    states=[sorted(v) for v in rev]
    ids=[{s:i for i,s in enumerate(ss)} for ss in states]
    E=[sorted((ids[d][t],x,ids[d][s]) for t,es in rev[d].items()
              for x,s in es if x) for d in range(2)]
    A=sorted((ids[0][l],ids[1][r]) for l,r in starts)
    W=sorted((list(l),list(r),*macro(l,r)) for l,r in starts)
    print('discovery',len(seen),sum(map(len,E)),list(map(len,states)),len(A))
    return dict(edges=E,sections=A,rules=W)

def encodeL(xs):return '00'+''.join('1'*a+'0' for a in xs)
def encodeR(xs):return ''.join('0'*b+'1'*c for b,c in map(unpair,xs))
def framed(q,l,r,lu,ru,n):
    def pop(s,u):
        if s:return int(s[0]),s[1:]
        assert not u,'unknown read'
        return 0,''
    for _ in range(n):
        a,l=pop(l,lu);w,d,q=P[2*q+a]
        if d:
            b,r=pop(r,ru);l=str(b)+str(w)+l
        else:r=str(w)+r
    return q,l,r
def same(s,t,u):return s==t if u else s.rstrip('0')==t.rstrip('0')

def verify(cert):
    # This function does not invoke discover or macro.
    # State 0 recognizes only empty stacks. Each inverse edge (t,x,s)
    # witnesses t accepting x::tail whenever s accepts tail.
    rev=[defaultdict(set),defaultdict(set)]
    fwd=[defaultdict(set),defaultdict(set)]
    for d,E in enumerate(cert['edges']):
        for t,x,s in E:
            assert t>0 and s>=0 and x>0
            if d==1:assert all(v>0 for v in unpair(x))
            rev[d][t].add((x,s));fwd[d][x,s].add(t)
    A=set(map(tuple,cert['sections']))
    W={}
    for lp,rp,k,lo,ro in cert['rules']:
        lp,rp,lo,ro=map(tuple,(lp,rp,lo,ro))
        assert 0<len(lp)<=2 and len(rp)<=3 and k>0
        assert lo and all(x>0 for x in lp+lo)
        assert all(all(v>0 for v in unpair(x)) for x in rp+ro)
        lu,ru=len(lp)==2,len(rp)==3
        q,l,r=framed(0,encodeL(lp),encodeR(rp),lu,ru,k)
        assert q==0 and same(l,encodeL(lo),lu) and same(r,encodeR(ro),ru)
        assert (lp,rp) not in W
        W[lp,rp]=(lo,ro)
    @lru_cache(None)
    def pops(d,s,k):
        if s==0:return (((),0),)
        if k==0:return (((),s),)
        return tuple(set(((x,*xs),u) for x,t in rev[d][s]
                         for xs,u in pops(d,t,k-1)))
    @lru_cache(None)
    def pushes(d,xs,s):
        T={s}
        for x in reversed(xs):T={t for u in T for t in fwd[d][x,u]}
        return T
    q,l,r=framed(0,'','',False,False,34)
    assert q==0 and same(l,encodeL((1,)),False) and same(r,encodeR((259,)),False)
    assert any((l,r) in A for l in pushes(0,(1,),0) for r in pushes(1,(259,),0))
    count=0
    for l,r in A:
        for lp,lt in pops(0,l,2):
            for rp,rt in pops(1,r,3):
                lo,ro=W[lp,rp]
                assert any((u,v) in A for u in pushes(0,lo,lt) for v in pushes(1,ro,rt))
                count+=1
    print('verified',len(W),'framed rules;',count,'tail combinations;',len(A),'sections')

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser()
    ap.add_argument('--read',help='verify a saved JSON certificate only')
    ap.add_argument('--write',help='write discovered JSON certificate')
    a=ap.parse_args()
    if a.read:
        with open(a.read) as f:cert=json.load(f)
    else:cert=discover()
    verify(cert)
    if a.write:
        with open(a.write,'w') as f:json.dump(cert,f,separators=(',',':'))
