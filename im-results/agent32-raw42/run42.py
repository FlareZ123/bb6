from collections import defaultdict, deque
from itertools import product
import json,sys

def stack_dfa(kind,params):
    k=params[0]
    if kind=='run':_,tz,to,pz,po=params;width=1;align=0
    else:_,width,t,m,align=params;tz=to=t;pz=po=m
    states=[((),0,0)];idx={states[0]:0};tr=[[-1,-1]]
    def push(i,b):
        if tr[i][b]>=0:return tr[i][b]
        runs,phase,partial=states[i]
        if i==0 and b==0:st=states[0]
        else:
            if i==0:phase=align
            partial=2*partial+b;phase+=1
            if phase==width:
                if runs and runs[0][0]==partial:
                    n=runs[0][1];t,m=(to,po) if partial and kind=='run' else (tz,pz)
                    runs=((partial,n+1 if n<t+m-1 else t),)+runs[1:]
                else:runs=((partial,1),)+runs[:k-1]
                phase=partial=0
            st=(runs,phase,partial)
        if st not in idx:idx[st]=len(states);states.append(st);tr.append([-1,-1])
        tr[i][b]=idx[st];return tr[i][b]
    return push,tr

def discover(table,kind,params,cap=20000,right=None):
    p=[table[i:i+3] for i in range(0,36,3)]
    push,tr=zip(stack_dfa(kind,params),stack_dfa(*(right or (kind,params))))
    edges=[defaultdict(set),defaultdict(set)];wait=[defaultdict(list),defaultdict(list)]
    seen={(0,0,0,0)};todo=deque(seen)
    for e in edges:e[0].add((0,0))
    def add(q,a,l,r):
        s=q,a,l,r
        if s not in seen:
            if len(seen)>=cap or p[2*q+a]=='---':raise ValueError
            seen.add(s);todo.append(s)
    def pop(s,b,x):
        q,a,l,r=s;w,d,n=p[2*q+a];w=int(w);n=ord(n)-65
        if d=='R':add(n,b,push[0](l,w),x)
        else:add(n,b,x,push[1](r,w))
    while todo:
        s=todo.popleft();q,a,l,r=s;w,d,n=p[2*q+a];w=int(w);side=int(d=='R');old=l if side else r;dest=push[1-side](old,w);e=w,old
        if e not in edges[1-side][dest]:
            edges[1-side][dest].add(e)
            for st in wait[1-side][dest]:pop(st,*e)
        x=r if side else l;wait[side][x].append(s)
        for b,y in sorted(edges[side][x]):pop(s,b,y)
    return [[max(0,x) for row in a for x in row] for a in tr],len(seen),[sorted((dst,b,src) for dst,es in e.items() for b,src in es) for e in edges],sorted(seen)

if __name__=='__main__':
    params=[]
    for k,t,m in product(range(1,5),range(1,4),range(1,5)):
        params.append(('run',(k,t,t,m,m)))
    for k,width,t,m in product(range(1,3),range(2,7),range(1,4),range(1,4)):
        for align in range(width):params.append(('block',(k,width,t,m,align)))
    params.sort(key=lambda x:(x[1][0]*x[1][1]*(x[1][2]+x[1][3]),len(x[1]),x[1]))
    for line in sys.stdin:
        id,s=line.split()
        for kind,p in params:
            try:d,n,_,_=discover(s,kind,p,3000)
            except ValueError:continue
            print(id,kind,*p,n,flush=True);break
        else:print(id,s,file=sys.stderr,flush=True)
