"""Search block-FAR parameters; this is a candidate generator, not a trusted decision procedure."""
from collections import defaultdict, deque
from functools import lru_cache
from itertools import product

def search(t,width,cap,mod,runs,flip=False,mode='runs',limit=50000,offset=0):
    moves=[None if v<=0 else ((v-1)//2%2,bool((v-1)%2)^flip,(v-1)//4) for v in t]
    @lru_cache(None)
    def macro(q,d,a):
        h=0 if d else width-1;seen=set()
        while 0<=h<width:
            k=q,h,a
            if k in seen:return None
            seen.add(k);mv=moves[2*q+(a>>h&1)]
            if mv is None:return None
            w,d,q=mv;a=(a&~(1<<h))|(w<<h);h+=1 if d else -1
        return q,d,a
    left=[()];leftids={():0};delta={};pred=defaultdict(list)
    nodes=[('T',)];nodeids={nodes[0]:0};edges=defaultdict(set);copier=defaultdict(set);pending=defaultdict(list);event=deque()
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
        key=l,a
        if key in delta:return delta[key]
        xs=left[l]
        if not xs and a==0:ys=()
        elif mode=='suffix':ys=(a,)+xs[:runs-1]
        elif xs and xs[0][0]==a:
            s,n,m=xs[0];ys=((s,min(cap,n+1),(m+1)%mod),)+xs[1:]
        else:ys=((a,1,1%mod),)+xs[:runs-1]
        if ys not in leftids:leftids[ys]=len(left);left.append(ys)
        j=leftids[ys];delta[key]=j;pred[j].append(key)
        for q,w,v in pending[j]:applyleft(l,a,q,w,v)
        return j
    push(0,0);add(0,0,0)
    if not offset:copy(ctrl(0,0,True),0)
    else:
        q,h,a=0,offset,0;seen=set()
        while 0<=h<width:
            k=q,h,a
            if k in seen:return None
            seen.add(k);mv=moves[2*q+(a>>h&1)]
            if mv is None:return None
            w,d,q=mv;a=(a&~(1<<h))|(w<<h);h+=1 if d else -1
        if d:copy(ctrl(push(0,a),q,True),0)
        else:
            init=node(('initial',));add(init,a,0);add(ctrl(0,q,False),0,init)
    count=0
    while event:
        s,a,v=event.popleft();count+=1
        if count>limit or len(event)>limit:return None
        for q in tuple(copier[s]):add(q,a,v)
        key=nodes[s]
        if key[0]!='c':continue
        _,l,q,d=key;m=macro(q,bool(d),a)
        if m is None:return None
        q2,d2,w=m
        if d2:copy(ctrl(push(l,w),q2,True),v)
        else:
            pending[l].append((q2,w,v))
            for l0,b in tuple(pred[l]):applyleft(l0,b,q2,w,v)
    return len(left),len(nodes),count

def discover(t):
    params=list(product(range(2,7),range(1,3),range(1,5),range(1,4),(False,True),('runs',)))
    params += [(w,1,1,r,f,'suffix') for w in range(2,7) for r in range(1,5) for f in (False,True)]
    params.sort(key=lambda p:p[0]*p[3]*(p[1]+p[2]))
    for p in params:
        if search(t,*p):return p
    raise ValueError(f'Unresolved block-FAR leaf: {t}')
