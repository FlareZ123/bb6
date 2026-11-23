"""Affine preimages of the original Machine C first-return section.

Each node (ac,ad,kc,kd) denotes (ac*u+ad,kc*u+kd) for all u>=0.
Only accepts uniform 2-adic valuations; ambiguity must be handled by
splitting a ray, never by asserting a result from a finite sample.
The companion generated Lean code formally checks every proposed parent.
"""
from collections import deque, Counter
def v2(x):
    if x <= 0: raise ValueError("v2 undefined at zero")
    return (x & -x).bit_length()-1
def parents(node):
    ac,ad,kc,kd=node
    if ad<0 or kd<5 or ac<0 or kc<0:return None,'small'
    if kc%2:return None,'ypar'
    sc,sd=ac+kc,ad+kd
    if sc%2:return None,'spar'
    q0=sd+(sd%2)
    if q0<=0:return None,'qzero'
    v=v2(q0)
    if sc%(1<<(v+1))!=0:return None,('vvar',v)
    if kd%2 and sd%4 not in (0,3):return [],'hole'
    ret=[]
    if kd%2==0:
        assert kc%2==0
        ret.append((sc,sd-2,kc//2,(kd-2)//2))
    for n in range(v-1):
        if n%2!=(0 if kd%2 else 1):continue
        shift=1<<(n+1)
        if sc%shift or q0%shift:return None,'notinteger'
        acoeff=sc//shift
        aconst=q0//shift-(2 if sd%2==0 else 3)
        kcoeff=sc+kc-acoeff
        kconst=sd+kd-aconst-7-3*n
        if kcoeff%2 or kconst%2:return None,'badpar'
        kcoeff//=2;kconst//=2
        if aconst<0 or kconst<0:return None,'negative'
        ret.append((acoeff,aconst,kcoeff,kconst))
    return ret,'ok'
def check(r,e,k0,depth=10,cap=1000):
    t0=r+(1<<e)
    start=(0,1,2048*(1<<e),2048*t0+k0)
    Q=deque([(start,0)]);seen={start};diag=Counter()
    while Q:
        node,d=Q.popleft()
        ps,why=parents(node)
        if ps is None:return False,d,why,len(seen),node
        diag[str(why)]+=1
        if d>=depth and ps:return False,d,'depth',len(seen),node
        for p in ps:
            if p not in seen:
                seen.add(p);Q.append((p,d+1))
                if len(seen)>cap:return False,d,'cap',len(seen),node
    return True,0,'closed',len(seen),diag
