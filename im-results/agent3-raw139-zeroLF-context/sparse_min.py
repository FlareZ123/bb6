"""Sparse bisimulation quotients and independent block-FAR closure checker."""
from collections import defaultdict, deque

def minimize(table,width,flip,result):
    _,_,_,_,(states,nodes,delta,edges)=result
    A=1<<width;N=len(nodes);D=len(states)
    rev=defaultdict(set);rows=defaultdict(lambda:defaultdict(set))
    for s,es in edges.items():
        for a,t in es:
            rows[s][a].add(t)
            if a==0:rev[t].add(s)
    zero={0};q=deque(zero)
    while q:
        for s in rev[q.popleft()]:
            if s not in zero:zero.add(s);q.append(s)
    def refine(N,signature):
        cls=[0]*N
        while True:
            ids={};new=[]
            for i in range(N):
                sig=signature(i,cls);new.append(ids.setdefault(sig,len(ids)))
            if new==cls:return cls,len(ids)
            cls=new
    rc,C=refine(N,lambda s,c:(s in zero,tuple((a,tuple(sorted({c[t] for t in ts}))) for a,ts in sorted(rows[s].items()))))
    dead=C;C+=1
    r2=defaultdict(set)
    for s,es in edges.items():
        for a,t in es:r2[rc[s],a].add(rc[t])
    ctrl={};aux={};cs=defaultdict(list);xs=defaultdict(list);ds=defaultdict(list)
    for i,node in enumerate(nodes):
        if node[0]=='c':
            _,l,q,d=node;ctrl[l,q,d]=rc[i];cs[l].append((q,d,rc[i]))
        elif node[0]=='x':
            _,p,b=node;_,l,q,d=nodes[p];assert d==0;aux[l,q,b]=rc[i];xs[l].append((q,b,rc[i]))
    for (l,a),j in delta.items():ds[l].append((a,j))
    sig=[(tuple(sorted(cs[l])),tuple(sorted(xs[l])),tuple(sorted(ds[l]))) for l in range(D)]
    lc,D2=refine(D,lambda l,c:(sig[l][:2],tuple((a,c[j]) for a,j in sig[l][2])))
    p2={};c2={};x2={}
    def put(m,k,v):
        assert k not in m or m[k]==v;m[k]=v
    for (l,a),j in delta.items():put(p2,(lc[l],a),lc[j]+1)
    for (l,q,d),j in ctrl.items():put(c2,(lc[l],q,d),j)
    for (l,q,b),j in aux.items():put(x2,(lc[l],q,b),j)
    pred=[[] for _ in range(D2)]
    for (l,a),j in sorted(p2.items()):pred[j-1].append(A*l+a)
    z2={rc[v] for v in zero};zn=[min(r2.get((v,0),set())&z2) if v in z2 else dead for v in range(C)]
    return dict(width=width,left_states=D2,right_nodes=C,push=p2,ctrl=c2,aux=x2,edges={k:sorted(v) for k,v in r2.items()},pred=pred,zero_states=sorted(z2),zeroNext=zn,moves=[None if t==24 else (t>>1&1,bool(t&1)!=flip,t>>2) for t in table])

def check(table,c,flip):
    A=1<<c['width'];W=c['width'];D=c['left_states'];N=c['right_nodes'];dead=N-1;push=c['push'];ctrl=c['ctrl'];aux=c['aux'];pred=c['pred'];edges=defaultdict(set,{k:set(v) for k,v in c['edges'].items()});zero=set(c['zero_states']);zn=c['zeroNext'];rows=defaultdict(dict)
    for (v,a),ts in edges.items():
        assert 0<=v<N and 0<=a<A and all(0<=t<N for t in ts)
        if ts:rows[v][a]=ts
    assert push[0,0]==1 and ctrl[0,0,1] in zero
    for v in zero:assert zn[v] in zero and zn[v] in rows[v].get(0,set())
    for (l,a),j in push.items():
        assert 0<=l<D and 0<=a<A and 1<=j<=D and l*A+a in pred[j-1]
    for j,ps in enumerate(pred):
        for p in ps:
            l,a=divmod(p,A);assert push[l,a]==j+1
    assert all(0<=v<N for v in ctrl.values()) and all(0<=v<N for v in aux.values())
    checked=0
    for (l,q,d),p in ctrl.items():
        for a,ts in rows[p].items():
            checked+=1;h=0 if d else W-1;b=a;qq=q;seen=set()
            while 0<=h<W:
                assert (h,b,qq) not in seen;seen.add((h,b,qq));x=table[2*qq+(b>>h&1)];assert x<24
                w=x>>1&1;qq=x>>2;dd=bool(x&1)!=flip;b=(b&~(1<<h))|(w<<h);h+=1 if dd else -1
            if dd:
                j=push[l,b]-1;p2=ctrl.get((j,qq,1),dead)
                for v in ts:
                    assert v not in zero or p2 in zero
                    for aa,tt in rows[v].items():assert tt<=rows[p2].get(aa,set())
            else:
                for pre in pred[l]:
                    j,aa=divmod(pre,A);p2=ctrl.get((j,qq,0),dead);x=aux.get((j,qq,aa),dead)
                    assert x in rows[p2].get(aa,set()) and ts<=rows[x].get(b,set())
    assert not rows[dead] and dead not in zero
    return checked,sum(map(len,edges.values()))
