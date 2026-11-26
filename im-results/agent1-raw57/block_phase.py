"""Untrusted block-suffix discovery and all-alignment lift to a primitive
two-stack certificate. The existing TwoSidedAutomata checker is the authority."""
from collections import defaultdict
from itertools import product

def macros(table,w):
    t=table.replace('_','')
    m=[t[i:i+3] for i in range(0,36,3)]
    out={}
    for q,d,b in product(range(6),range(2),range(1<<w)):
        h=0 if d else w-1
        z,s,n=b,q,0
        while 0<=h<w and n<=6*w*(1<<w):
            a=m[2*s+((z>>h)&1)]
            if a=='---': break
            z=(z&~(1<<h))|(int(a[0])<<h)
            dr=int(a[1]=='R')
            s=ord(a[2])-65
            h+=1 if dr else -1
            n+=1
        if not 0<=h<w:
            out[q,d,b]=(s,dr,z,n)
    return out

def closure(exit_fn,push_fn,blank=((),()),limit=1000000):
    tab=[[blank[0]],[blank[1]]]
    ids=[{blank[0]:0},{blank[1]:0}]
    D=[{},{}]
    edges=[defaultdict(set),defaultdict(set)]
    wait=[defaultdict(list),defaultdict(list)]
    for e in edges: e[0].add((0,0))
    start=(0,1,0,0,0)
    seen={start};todo=[start];fail=False
    def add(x):
        nonlocal fail
        if x not in seen:
            seen.add(x);todo.append(x)
            if len(todo)>=limit or exit_fn(*x[:3]) is None: fail=True
    def pop(x,edge,j):
        q,d,b,l,r=x
        qq,dd,ww,n=exit_fn(q,d,b)
        c,pre=edge
        add((qq,dd,c,j,pre) if dd else (qq,dd,c,pre,j))
    def push(d,i,b):
        if (i,b) in D[d]: return D[d][i,b]
        y=push_fn(d,tab[d][i],b)
        j=ids[d].get(y)
        if j is None:
            j=len(tab[d]);tab[d].append(y);ids[d][y]=j
        D[d][i,b]=j
        return j
    for x in todo:
        q,d,b,l,r=x
        ex=exit_fn(q,d,b)
        if ex is None:
            fail=True;break
        qq,dd,w,n=ex
        side=1-dd;old=r if side else l;z=l if side else r
        j=push(side,old,w);e=(w,old)
        if e not in edges[side][j]:
            edges[side][j].add(e)
            for c,k in wait[side][j]:
                pop(c,e,k)
                if fail:break
        if fail:break
        wait[1-side][z].append((x,j))
        for ee in edges[1-side][z]:
            pop(x,ee,j)
            if fail:break
        if fail:break
    return not fail,len(todo),edges,seen,D,tab

def block(table,w,dl,dr):
    ms=macros(table,w)
    def push(d,x,b):
        return x if not x and b==0 else (b,)+x[:(dr if d else dl)-1]
    return closure(lambda q,d,b:ms.get((q,d,b)),push)

def phase_lift(table,w,c,limit=500000,missing=0):
    D=c[4]
    initial=tuple((0,0) for _ in range(w))
    def push(side,old,b):
        res=[None]*w
        for p,(q,v) in enumerate(old):
            v=v|b<<p if side==0 else (v<<1)|b
            if p+1==w: res[0]=(D[side].get((q,v),missing),0)
            else: res[p+1]=(q,v)
        return tuple(res)
    p=table.replace('_','')
    def ex(q,d,b):
        a=p[6*q+3*b:6*q+3*b+3]
        if a=='---': return None
        return ord(a[2])-65,int(a[1]=='R'),int(a[0]),1
    ok,n,E,S,D,T=closure(ex,push,(initial,initial),limit)
    S={(q,b,l,r) for q,d,b,l,r in S}
    return ok,len(S),E,S,D,T

def run(table,w,dl,dr,missing=0):
    c=block(table,w,dl,dr)
    assert c[0],(table,w,dl,dr,c[1])
    cert=phase_lift(table,w,c,missing=missing)
    assert cert[0],(table,w,dl,dr,cert[1])
    print('block/phase counts',c[1],cert[1],flush=True)
    return cert
