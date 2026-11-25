from collections import defaultdict, deque
from functools import lru_cache
def generate(table,width=2,cap=2,mod=4,runs=2,flip=False,event_limit=150000,phase=False):
    alphabet=2**width
    moves=[None if n==24 else ((n>>1)&1,bool(n&1)!=flip,n>>2) for n in table]
    @lru_cache(None)
    def macro(q,d,a):
        h=0 if d else width-1
        seen=set()
        while 0<=h<width:
            k=(q,h,a)
            if k in seen:return None
            seen.add(k);mv=moves[2*q+(a>>h&1)]
            if mv is None:return None
            w,d,q=mv;a=(a&~(1<<h))|(w<<h);h+=1 if d else -1
        return q,d,a
    left=[()];leftids={():0};delta={};pred=defaultdict(list)
    nodes=[('T',)];nodeids={nodes[0]:0};edges=defaultdict(set);copier=defaultdict(set);pending=defaultdict(set);event=deque()
    def node(key):
        if key not in nodeids:nodeids[key]=len(nodes);nodes.append(key)
        return nodeids[key]
    def ctrl(l,q,d):return node(('c',l,q,int(d)))
    def add(s,a,t):
        if (a,t) not in edges[s]:edges[s].add((a,t));event.append((s,a,t))
    def copy(q,v):
        if q not in copier[v]:
            copier[v].add(q)
            for a,t in tuple(edges[v]):add(q,a,t)
    def applyleft(l0,b,q,w,v):
        p=ctrl(l0,q,False);x=node(('x',p,b));add(x,w,v);add(p,b,x)
    def push(l,a):
        key=(l,a)
        if key in delta:return delta[key]
        xs=left[l]
        if not xs and a==0:ys=()
        elif phase:
            ys=((a,)+xs[0][:runs-1] if xs else (a,), ((xs[1] if xs else 0)+1)%mod)
        elif xs and xs[0][0]==a:
            s,n,m=xs[0];ys=((s,min(cap,n+1),(m+1)%mod),)+xs[1:]
        else:ys=((a,1,1%mod),)+xs[:runs-1]
        if ys not in leftids:leftids[ys]=len(left);left.append(ys)
        j=leftids[ys];delta[key]=j;pred[j].append(key)
        for q,w,v in pending[j]:applyleft(l,a,q,w,v)
        return j
    push(0,0);add(0,0,0);copy(ctrl(0,0,True),0)
    count=0
    while event:
        s,a,v=event.popleft();count+=1
        if count>event_limit:return None
        for q in tuple(copier[s]):add(q,a,v)
        key=nodes[s]
        if key[0]!='c':continue
        _,l,q,d=key;m=macro(q,bool(d),a)
        if m is None:return None
        q2,d2,w=m
        if d2:copy(ctrl(push(l,w),q2,True),v)
        elif (q2,w,v) not in pending[l]:
            pending[l].add((q2,w,v))
            for l0,b in pred[l]:applyleft(l0,b,q2,w,v)
    zero={0};rev=defaultdict(list)
    for s,es in edges.items():
        for a,t in es:
            if a==0:rev[t].append(s)
    zq=deque(zero)
    while zq:
        for s in rev[zq.popleft()]:
            if s not in zero:zero.add(s);zq.append(s)
    D,N=len(left),len(nodes)
    rows=defaultdict(set)
    for s,es in edges.items():
        for a,t in es:rows[s,a].add(t)
    cls=[int(s in zero) for s in range(N)]
    while True:
        keys={};new=[]
        for s in range(N):
            k=(s in zero,tuple(tuple(sorted({cls[t] for t in rows[s,a]})) for a in range(alphabet)))
            new.append(keys.setdefault(k,len(keys)))
        if new==cls:break
        cls=new
    dead=len(set(cls));C=dead+1
    r2=defaultdict(set);z2={cls[s] for s in zero}
    for (s,a),ts in rows.items():r2[cls[s],a].update(cls[t] for t in ts)
    ctr={tuple(rest):cls[i] for i,(k,*rest) in enumerate(nodes) if k=='c'}
    aux={}
    for i,(k,*rest) in enumerate(nodes):
        if k=='x':
            p,b=rest;_,l,q,d=nodes[p];aux[l,q,d,b]=cls[i]
    # Preserve all control/auxiliary identities while minimizing left DFA.
    sig=[tuple(ctr.get((l,q,d),dead) for q in range(6) for d in range(2))+tuple(aux.get((l,q,0,b),dead) for q in range(6) for b in range(alphabet)) for l in range(D)]
    lc=[0]*D
    while True:
        keys={};new=[]
        for l in range(D):
            k=(sig[l],tuple(lc[delta[l,a]] if (l,a) in delta else -1 for a in range(alphabet)))
            new.append(keys.setdefault(k,len(keys)))
        if new==lc:break
        lc=new
    D2=len(set(lc))
    delta={(lc[l],a):lc[j] for (l,a),j in delta.items()}
    ctr={(lc[l],q,d):v for (l,q,d),v in ctr.items()}
    aux={(lc[l],q,d,b):v for (l,q,d,b),v in aux.items()}
    D=D2;pred=defaultdict(list)
    for (l,a),j in sorted(delta.items()):pred[j].append((l,a))
    assert delta[0,0]==0 and ctr[0,0,1] in z2
    zeroNext=[min(r2[s,0]&z2) if s in z2 else dead for s in range(C)]
    for l in range(D):
        for q in range(6):
            for d in range(2):
                p=ctr.get((l,q,d),dead)
                for a in range(alphabet):
                    ts=r2[p,a]
                    if not ts:continue
                    q2,d2,w=macro(q,bool(d),a)
                    if d2:
                        p2=ctr[delta[l,w],q2,1]
                        for v in ts:
                            assert v not in z2 or p2 in z2
                            assert all(r2[v,b]<=r2[p2,b] for b in range(alphabet))
                    else:
                        for l0,b in pred[l]:
                            p2=ctr[l0,q2,0];x=aux[l0,q2,0,b]
                            assert x in r2[p2,b] and ts<=r2[x,w]
    return dict(width=width,moves=moves,left_states=D,right_nodes=C,
        push=[1+delta[l,a] if (l,a) in delta else 0 for l in range(D) for a in range(alphabet)],
        ctrl=[ctr.get((l,q,d),dead) for l in range(D) for q in range(6) for d in range(2)],
        aux=[aux.get((l,q,0,b),dead) for l in range(D) for q in range(6) for b in range(alphabet)],
        edges=[sorted(r2[s,a]) for s in range(C) for a in range(alphabet)],
        zeroNext=zeroNext,zero_states=sorted(z2),pred=[[alphabet*l+a for l,a in pred[j]] for j in range(D)])
