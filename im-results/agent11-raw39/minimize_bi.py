"""Joint context/transition partition refinement of finite stack automata."""
from collections import defaultdict,deque
def reach(table,ds,cap=100000):
    p=table.replace('_','');p=[p[i:i+3] for i in range(0,36,3)]
    edges=[defaultdict(set),defaultdict(set)];waiting=[defaultdict(list),defaultdict(list)]
    todo=deque([(0,0,0,0)]);seen=set(todo)
    for e in edges:e[0].add((0,0))
    def add(q,a,l,r):
        s=(q,a,l,r)
        if s not in seen:
            if p[2*q+a]=='---':raise ValueError('hole')
            seen.add(s);todo.append(s)
            if len(seen)>cap:raise ValueError('cap')
    def pop(s,b,src):
        q,a,l,r=s;m=p[2*q+a];w,n=int(m[0]),ord(m[2])-65
        if m[1]=='R':add(n,b,ds[0][2*l+w],src)
        else:add(n,b,src,ds[1][2*r+w])
    while todo:
        s=todo.popleft();q,a,l,r=s;m=p[2*q+a];assert m!='---'
        w=int(m[0]);side=int(m[1]=='R');old=l if side else r;dest=ds[1-side][2*old+w];e=(w,old)
        if e not in edges[1-side][dest]:
            edges[1-side][dest].add(e)
            for st in waiting[1-side][dest]:pop(st,*e)
        x=r if side else l;waiting[side][x].append(s)
        for b,y in sorted(edges[side][x]):pop(s,b,y)
    return seen,edges

def minimize(table,ds):
    seen,_=reach(table,ds)
    old=[[0]*(len(d)//2) for d in ds]
    while True:
        c=[[set() for _ in o] for o in old]
        for q,a,l,r in seen:
            c[0][l].add((q,a,old[1][r]));c[1][r].add((q,a,old[0][l]))
        nxt=[]
        for side in range(2):
            ids={};group=[]
            for i,ctx in enumerate(c[side]):
                key=(old[side][i],frozenset(ctx),old[side][ds[side][2*i]],old[side][ds[side][2*i+1]])
                group.append(ids.setdefault(key,len(ids)))
            nxt.append(group)
        if old==nxt:break
        old=nxt
    nd=[]
    for i in range(2):
        a=[0]*(2*(max(old[i])+1))
        for j,v in enumerate(ds[i]):a[2*old[i][j//2]+j%2]=old[i][v]
        nd.append(a)
    ns,ne=reach(table,nd)
    return nd[0],nd[1],len(ns),sum(len(v) for es in ne for v in es.values())
