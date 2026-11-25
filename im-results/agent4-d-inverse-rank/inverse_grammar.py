"""Demand-driven exact first-left-exit inverse for literal Cryptid D.

The output rank never increases along a demanded subgoal. The only required
termination theorem is the original-source R(input) <= R(output)+4.
"""
from collections import defaultdict, deque
from functools import lru_cache

RULES=((1,1,1),(0,1,4),(1,-1,2),(0,1,0),(1,-1,0),(1,-1,3),
       (1,-1,2),(1,-1,5),(0,-1,2),(0,-1,1),(1,-1,4),None)
F=(4,4,6,4,4,6,4,4,4,4,4,4,4,4,5,5)
@lru_cache(maxsize=1000000)
def rank(w):
    n=0
    while w:n+=F[w&15];w>>=1
    return n

LEFT=[[] for _ in range(6)];RIGHT=[[] for _ in range(2)]
for i,ins in enumerate(RULES):
    if ins is None:continue
    b,d,r=ins
    if d<0:LEFT[r].append((i//2,i%2,b))
    else:RIGHT[b].append((i//2,i%2,r))

@lru_cache(maxsize=100000)
def inverse_exit(r,y):
    """Return all (input state, word) yielding exactly (r,y) at first left exit."""
    root=(r,y); cap=rank(y)
    ans={}; subs=defaultdict(set); todo=deque()
    def demand(g):
        if g in ans:return
        assert rank(g[1])<=cap
        ans[g]=set()
        s,z=g
        for q,b,v in LEFT[s]:
            if z&1==v:add(g,(q,(z&~1)|b))
    def add(g,x):
        if rank(x[1])>rank(g[1])+4:return
        if x not in ans[g]:
            ans[g].add(x);todo.append((g,x))
    def extend(parent,q,b,required,x):
        q1,w=x
        if q1==required:add(parent,(q,2*w+b))
    demand(root)
    while todo:
        g,x=todo.popleft()
        for parent,q,b,required in tuple(subs[g]):extend(parent,q,b,required,x)
        s,z=x
        for q,b,r1 in RIGHT[z&1]:
            h=(s,z>>1)
            assert rank(h[1])<=rank(g[1])
            demand(h)
            sub=(g,q,b,r1)
            if sub not in subs[h]:
                subs[h].add(sub)
                for t in tuple(ans[h]):extend(g,q,b,r1,t)
    return frozenset(ans[root])

@lru_cache(maxsize=100000)
def old_inverse(r,y):
    rev=[[] for _ in range(6)]
    for i,ins in enumerate(RULES):
        if ins is not None:
            b,d,q=ins;rev[q].append((i//2,i%2,b,d))
    ry=rank(y);head_bound=6*((ry+4)//4)+7
    start=(r,-1,y);todo=deque([start]);seen={start};out=set()
    while todo:
        q,h,w=todo.popleft()
        if h==0 and rank(w)<=ry+4:out.add((q,w))
        for a,b,v,d in rev[q]:
            g=h-d
            if 0<=g<=head_bound and (w>>g)&1==v:
                c=(a,g,w^((b^v)<<g))
                if c not in seen:seen.add(c);todo.append(c)
    return frozenset(out)

if __name__=='__main__':
    from time import perf_counter
    from evaluator import first_exit
    def decode(w):return bin(w)[2:][::-1] if w else ''
    def encode(w):return int(w[::-1],2) if w else 0
    limit=1<<10
    targets=defaultdict(set)
    for q in range(6):
        for w in range(limit):
            a=first_exit(q,decode(w))
            if a is not None:targets[a[0],encode(a[1])].add((q,w))
    t=perf_counter()
    inv={g:inverse_exit(*g) for g in targets}
    print('new seconds',perf_counter()-t,'fibers',len(inv),flush=True)
    for g,ps in inv.items():
        assert {x for x in ps if x[1]<limit}==targets[g]
        assert all(first_exit(q,decode(w))==(g[0],decode(g[1])) for q,w in ps)
    t=perf_counter()
    for g,ps in inv.items():assert old_inverse(*g)==ps,(g,ps,old_inverse(*g))
    print('old seconds',perf_counter()-t,'all equal',flush=True)
