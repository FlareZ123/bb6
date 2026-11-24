"""Exact finite inverse of the D selected-section recurrence.

Canonical integer suffix: scanned bit least significant, implicit zero tail.
The proof of termination uses the four-bit lower rank theorem and Agent2's
original-source first-exit space bound, not an arbitrary simulation cap.
"""
from collections import deque
from functools import lru_cache
from evaluator import RULES, step, e_step
from lowrank import rank

REV = [[] for _ in range(6)]
for i, ins in enumerate(RULES):
    if ins is not None:
        b,d,q = ins
        REV[q].append((i//2,i%2,b,d))
GUARD = (0,0,1,0,1,0,1,0)

def encode(w):
    return int(w[::-1],2) if w else 0

def decode(w):
    return bin(w)[2:][::-1] if w else ''

def sweep(q,w,p):
    return p>=2 and p%2==0 and q in (1,3) and w%2==0

@lru_cache(maxsize=100000)
def reverse_exit(r,y):
    """All first-left exits ending in (r,y), with initial head at cell 0.

    If x is an actual input, 4*width(x)<=rank(y)+4. The original source
    first-event bound gives head<=2*R_old(x)+7<=6*width(x)+7 throughout.
    The reverse path never changes cells beyond max(head_bound,width(y)-1).
    Hence the queue is finite and contains every valid predecessor path.
    """
    ry=rank(y)
    width_bound=(ry+4)//4
    head_bound=6*width_bound+7
    start=(r,-1,y)
    todo=deque([start]); seen={start}; out=set()
    while todo:
        q,h,w=todo.popleft()
        if h==0 and rank(w)<=ry+4:
            out.add((q,w))
        for a,b,v,d in REV[q]:
            g=h-d
            if 0<=g<=head_bound and (w>>g)&1==v:
                c=(a,g,w^((b^v)<<g))
                if c not in seen:
                    seen.add(c);todo.append(c)
    return frozenset(out)

def e_type(s):
    """Necessary, disjoint output-prefix types (p,q,offset,rank gain)."""
    if s%16==10:return 4,3,9,3
    if s%128==126 or s%256==222:return 6,1,5,21
    if s%256==94 and s>=256:return 8,1,3,31
    return None

@lru_cache(maxsize=100000)
def e_inverse(s):
    """Return (offset, complete finite set of input suffixes), or (None,empty).

    Success iff one exact finite guard path in reverse reaches E with scanned 0.
    """
    typ=e_type(s)
    if typ is None:return None,frozenset()
    p,q,c,gain=typ
    end=8*s+6 if p==4 else 2*s
    frontier={(q,end)}
    for j in range(p-1,-1,-1):
        frontier={(q,w) for r,z in frontier if z%2==GUARD[j]
                  for q,w in reverse_exit(r,z//2) if not sweep(q,w,j)}
    bound=rank(s)-gain
    return c,frozenset(w for q,w in frontier if q==4 and w%2==0 and rank(w)<=bound)

@lru_cache(maxsize=None)
def token_count(d):
    """Number of code words of weight d, weights of 10 and 111 are 1 and 4."""
    if d<0:return 0
    if d==0:return 1
    return token_count(d-1)+token_count(d-4)

def tokens(d):
    if d==0:yield ''
    if d>=1:
        for v in tokens(d-1):yield '10'+v
    if d>=4:
        for v in tokens(d-4):yield '111'+v

def preimage_families(N,s):
    """Yield disjoint symbolic families (n,kind,code_weight,l or E input).

    For B: w=0 1^l s. For A: w=0 code(d) 0 1^l s.
    For AE: w=0 code(d) 11 w_E. All interpreted with implicit zeros.
    For E: w=w_E. These formulas include all n>=2.
    """
    ec,ew=e_inverse(s)
    for k in range(N//8+1):
        c=N-8*k
        if c>=9:yield 3*k+2,'B',0,c-9
        if c==ec:
            for w in ew:yield 3*k+4,'E',0,w
        if c>=11:
            for d in range((c-11)//2+1):
                yield 3*k+3,'A',d,c-11-2*d
        if ec is not None and c>=ec+2 and (c-ec-2)%2==0:
            d=(c-ec-2)//2
            for w in ew:yield 3*k+3,'AE',d,w

def predecessors(N,s):
    """Materialize all predecessors; preimage_families avoids huge token lists."""
    tail=decode(s)
    for n,kind,d,a in preimage_families(N,s):
        if kind=='B':yield n,encode('0'+'1'*a+tail)
        elif kind=='E':yield n,a
        elif kind=='A':
            for u in tokens(d):yield n,encode('0'+u+'0'+'1'*a+tail)
        else:
            for u in tokens(d):yield n,encode('0'+u+'11'+decode(a))

def forward(n,w):
    r=n%3;result=step(decode(w),r)
    if result is None:return None
    c,s=result
    return 8*((n-(3,4,2)[r])//3)+c,encode(s)

def test():
    # Bounded forward-vs-inverse check is just a regression of the exact algorithm.
    e={}
    for w in range(0,1<<12,2):
        a=e_step(decode(w))
        if a is not None:
            c,s=a;s=encode(s)
            assert c==e_type(s)[2]
            e.setdefault(s,set()).add(w)
    for s,ws in e.items():
        c,ps=e_inverse(s)
        assert {w for w in ps if w<1<<12}==ws,(s,ws,ps)
        assert all(e_step(decode(w))==(c,decode(s)) for w in ps)
    print('E inverse checked',len(e),'output fibers',sum(map(len,e.values())),'successful input words')
    targets={forward(n,w) for n in range(2,13) for w in range(0,1<<6,2)}-{None}
    for N,s in targets:
        ps=set(predecessors(N,s))
        assert all(forward(n,w)==(N,s) for n,w in ps)
        ws={(n,w) for n in range(2,13) for w in range(0,1<<6,2) if forward(n,w)==(N,s)}
        assert {(n,w) for n,w in ps if n<=12 and w<1<<6}==ws
    print('section inverse checked',len(targets),'target sections')

if __name__=='__main__':test()
