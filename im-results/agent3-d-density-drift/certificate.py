"""Finite max-plus abstract checker; all numbers are exact integers."""
from functools import lru_cache
K=11;M=1<<K;N=2*M
CLASSES=range(N);CANON=range(0,N,2)
RULES=((1,1,1),(0,1,4),(1,-1,2),(0,1,0),(1,-1,0),(1,-1,3),(1,-1,2),(1,-1,5),(0,-1,2),(0,-1,1),(1,-1,4),None)

def rank_short(c):
    return c.bit_length()+2*sum(((c>>i)&7)==6 for i in range(c.bit_length()))

def lower(c):
    if c<M:return rank_short(c)
    return K+1

def head(c):return c&1

def put(d,k,v):
    if d.get(k,-10**9)<v:d[k]=v;return True
    return False

@lru_cache(None)
def pop(c):
    if c<M:return ((c//2,rank_short(c//2)-rank_short(c)),)
    p=c-M;d=-1-2*(p%8==6);q=p//2
    return ((q+M//2,d),(q+M,d),(q+M+M//2,d))

@lru_cache(None)
def push(b,c):
    if c==0:return b,b
    if c<M and 2*c+b<M:return 2*c+b,1+2*(b==0 and c%4==3)
    return M+(2*c+b)%M,1+2*(b==0 and c%4==3)

@lru_cache(None)
def replace(b,c):
    if c<M:
        q=2*(c//2)+b;return q,rank_short(q)-rank_short(c)
    q=2*(c//2)+b;return q,2*((q%8==6)-(c%8==6))

@lru_cache(None)
def drop(c,k):
    if k==0:return {c:0}
    out={}
    for j,g in pop(c):
        for l,h in drop(j,k-1).items():put(out,l,g+h)
    return out

@lru_cache(None)
def canon(c):
    if not head(c):return {c:0}
    if c==N-1:return {j:-K for j in CANON}
    out={}
    for j,g in pop(c):
        for k,h in canon(j).items():put(out,k,g+h)
    return out

@lru_cache(None)
def popcanon(c):
    out={}
    for j,g in pop(c):
        for k,h in canon(j).items():put(out,k,g+h)
    return out


def exit_rows():
    X=[[{} for c in CLASSES] for q in range(6)]
    for q in range(6):
        for c in CLASSES:
            ins=RULES[2*q+head(c)]
            if ins is None:continue
            b,d,r=ins
            if d<0:
                j,g=replace(b,c);X[q][c][r,j]=g
    rounds=0
    while True:
        changed=0;rounds+=1
        for q in (0,1):
            for c in CLASSES:
                b,d,r=RULES[2*q+head(c)]
                if d<0:continue
                out=X[q][c]
                for j,g1 in pop(c):
                    for (r2,k),g2 in list(X[r][j].items()):
                        l,g3=push(b,k)
                        for (r3,m),g4 in list(X[r2][l].items()):
                            changed+=put(out,(r3,m),g1+g2+g3+g4)
        if not changed:break
    return X,rounds


def check_exit(X):
    for q in range(6):
        for c in CLASSES:
            ins=RULES[2*q+head(c)]
            if ins is None:continue
            b,d,r=ins
            if d<0:
                j,g=replace(b,c);assert X[q][c][r,j]>=g
            else:
                for j,g1 in pop(c):
                    for (r2,k),g2 in X[r][j].items():
                        l,g3=push(b,k)
                        for (r3,m),g4 in X[r2][l].items():
                            assert X[q][c][r3,m]>=g1+g2+g3+g4


def e_rows(X):
    E=[{} for c in CLASSES];guard=(0,0,1,0,1,0,1,0)
    max_guard_gain_minus_p=-10**9
    for c in CANON:
        cur={(4,c):0}
        for p in range(9):
            nxt={}
            for (q,j),g in cur.items():
                if p>=2 and p%2==0 and q in (1,3) and head(j)==0:
                    max_guard_gain_minus_p=max(max_guard_gain_minus_p,g-p)
                    for k,h in popcanon(j).items():put(E[c],k,g+h)
                    continue
                if q==5 and head(j):continue
                assert p<len(guard),(c,q,j,g)
                for (r,k),h in X[q][j].items():
                    l,h2=push(guard[p],k);put(nxt,(r,l),g+h+h2)
            cur=nxt
    assert max_guard_gain_minus_p==4
    print('E guard gain minus consumed length',max_guard_gain_minus_p,flush=True)
    return E


def a_edges(c):
    if (c>>1)&1==0:return 'close',drop(c,2)
    if (c>>2)&1==0:k=3
    elif (c>>3)&1:k=4
    else:return 'E',drop(c,3)
    out={}
    for j,g in drop(c,k).items():
        l,h=push(0,j);put(out,l,g+h)
    return 'token',out


def compose_value(edges,V,scale):
    return max((scale*g+V[j] for j,g in edges.items()),default=-10**9)



def a_rows(E):
    A=[{} for _ in CLASSES];T={}
    for c in CANON:
        kind,edges=a_edges(c)
        if kind=='token':T[c]=edges
        elif kind=='close':
            for j,g in edges.items():
                for k,h in canon(j).items():put(A[c],k,g+h)
        else:
            for j,g in edges.items():
                for k,h in E[j].items():put(A[c],k,g+h)
    rounds=0
    while True:
        rounds+=1;changed=False
        for c,edges in T.items():
            for j,g in edges.items():
                for k,h in list(A[j].items()):changed|=put(A[c],k,g+h)
        if not changed:break
    return A,rounds

def check_a(A,E):
    for c in CANON:
        kind,edges=a_edges(c)
        for j,g in edges.items():
            for k,h in (canon(j) if kind=='close' else E[j] if kind=='E' else A[j]).items():
                assert A[c][k]>=g+h

def check_full():
    X,rounds=exit_rows();check_exit(X);print('X',rounds,sum(len(d) for row in X for d in row),flush=True)
    E=e_rows(X);A,rounds=a_rows(E);check_a(A,E);B=[popcanon(c) if c in CANON else {} for c in CLASSES]
    for label,table in zip('AEB',[A,E,B]):
        gains=[g for c in CANON for g in table[c].values()]
        assert -18<=min(gains)<=max(gains)<=11
        print(label,len(gains),min(gains),max(gains),flush=True)
    V=[0]*N
    for d in range(1,6):
        scale=3**(d-1); W=[0]*N
        for c in CANON:W[c]=sum(max(-scale*lower(c),compose_value(t[c],V,scale)) for t in (A,E,B))
        V=W
        print('drift',d,max(V[c] for c in CANON if c>=M),flush=True)
    assert max(V[c] for c in CANON if c>=M)<=-118
    return A,E,B


if __name__=='__main__':
    from fractions import Fraction as F
    from evaluator import step
    check_full()
    route='EEEBBBEEEBEEEBBBEEEBBBBEEEBBBEEEEBBBBBEEEEBBBBEEEEBBBEEEBBBEEEBBBBEEEBBBEEEEBBBBBEEEEBBBBBEEEEBBBBEEEEBBBBBE'
    assert len(route)==108
    n=536381281436517453494167225374698024519484110452372
    w=''
    for i,ch in enumerate(route):
        r='AEB'.index(ch);assert n%3==r
        ans=step(w,r)
        if i==len(route)-1:assert ans is None;break
        assert ans is not None
        c,w=ans;assert c>=3
        n=8*((n-(3,4,2)[r])//3)+c
    print('108-step halting cylinder checked')
    a=F(100001,100000);q=F(249999,250000)
    assert max(lower(c) for c in CANON if c<M)==17
    for g in range(-90,56):assert a**g<=1+F(g,100000)+F(4095,10**10)
    assert 1-F(118,243*100000)+F(4095,10**10)<=q
    assert a**1337<2
    print('exponential moment inequalities checked')
    anchors=[]
    for n,count in ((5,10),(9,10),(15,10),(39,9)):
        w=''
        for _ in range(count):
            r=n%3;ans=step(w,r);assert ans is not None
            c,w=ans;n=8*((n-(3,4,2)[r])//3)+c
        R=rank_short(int(w[::-1],2)) if w else 0
        anchors.append((n,R))
    assert anchors==[(123501,9),(196699,0),(276715,0),(277451,0)]
    L=[5*n-23 for n,R in anchors]
    U=[5*(n+R)+27 for n,R in anchors]
    assert all(U[i]<L[i+1] for i in range(3))
    assert 3*U[-1]<8*L[0]
    print('four separated phase bands',list(zip(L,U)))
