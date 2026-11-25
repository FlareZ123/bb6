"""Candidate finite stack-relation generation. No trust in search is required."""
from collections import defaultdict

def pushfun(n,cap,mod):
    # 0 denotes the infinite bottom zero run; positive runs use a saturated
    # length or a cyclic length class once cap is reached.
    def push(x,b):
        bit,runs=x
        if bit!=b:return (b,(1,)+runs[:n-1])
        j=runs[0]
        if j==0:return x
        jj=j+1 if j<cap+mod-1 else cap
        return (b,(jj,)+runs[1:])
    return push

def check(p,paramsL,paramsR,limit=150000):
    P=[pushfun(*paramsL),pushfun(*paramsR)]
    blank=(0,(0,));tab=[[blank],[blank]];ids=[{blank:0},{blank:0}];D=[{},{}]
    def dfa(d,i,b):
        k=(i,b)
        if k in D[d]:return D[d][k]
        y=P[d](tab[d][i],b);j=ids[d].get(y)
        if j is None:j=len(tab[d]);tab[d].append(y);ids[d][y]=j
        D[d][k]=j;return j
    edges=[defaultdict(set),defaultdict(set)]
    wait=[defaultdict(list),defaultdict(list)]
    for e in edges:e[0].add((0,0))
    seen={(0,0,0,0)};todo=[(0,0,0,0)];failure=False;capped=False
    def add(x):
        nonlocal failure,capped
        if x not in seen:
            seen.add(x);todo.append(x)
            if p[2*x[0]+x[1]]=='---':failure=True
            if len(todo)>=limit:capped=True
    def pop(x,edge,pushed):
        q,b,l,r=x;m=p[2*q+b];s=ord(m[2])-65;c,pre=edge
        if m[1]=='R':add((s,c,pushed,pre))
        else:add((s,c,pre,pushed))
    def addEdge(d,x,b,pre):
        if (b,pre) in edges[d][x]:return
        e=(b,pre);edges[d][x].add(e)
        for c,j in wait[d][x]:
            pop(c,e,j)
            if failure or capped:return
    i=0
    while i<len(todo) and not failure and not capped:
        c=todo[i];i+=1;q,b,l,r=c;m=p[2*q+b];w=int(m[0]);d=m[1]=='L'
        x=(r if d else l);j=dfa(d,x,w);addEdge(d,j,w,x)
        z=l if d else r;wait[1-d][z].append((c,j))
        for e in edges[1-d][z]:
            pop(c,e,j)
            if failure or capped:break
    return not failure and not capped,len(todo),edges,seen,D,tab
