"""First-hole enumeration of the six exact-one-halt slices of Raw10 box 15.
Run with python search_box15.py 1 7 8 9 10 11 from a scratch directory.
Outputs are exploratory certificates, not trusted proof leaves.
"""
from collections import defaultdict, Counter
from pathlib import Path
from math import prod
import sys, time, json
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'agent13-raw10-box17'))
from box17 import trace
DOM=[[8],list(range(25)),[11],[6],[17],[13],[11],list(range(25)),[0,3,4,12,18,20,21,22,23,24],list(range(25)),list(range(25)),list(range(25))]

def domain_check(ds,k,cap=2000):
    mask=(1<<k)-1; shift=k-1
    todo=[(0,0,0)]; seen=set(todo); edges=[{0:1},{0:1}]; waiting=[defaultdict(list),defaultdict(list)]
    def add(s,l,r):
        x=(s,l,r)
        if x not in seen:
            if 0 in ds[s]:raise ValueError
            if len(seen)>=cap:raise OverflowError
            seen.add(x);todo.append(x)
    def pop(x,v,e):
        s,l,r=x;v-=1;q=v//4;w=v//2%2
        if v%2:add(2*q+(r&1),((l<<1)|w)&mask,(r>>1)|(e<<shift))
        else:add(2*q+(l&1),(l>>1)|(e<<shift),((r<<1)|w)&mask)
    def edge(d,x,e):
        old=edges[d].get(x,0)
        if old&(1<<e):return
        edges[d][x]=old|(1<<e)
        for y,v in waiting[d][x]:pop(y,v,e)
    try:
        for x in todo:
            s,l,r=x
            for val in ds[s]:
                if val==0:return None
                v=val-1;w=v//2%2;d=v%2;u,y=(l,r) if d else (r,l)
                edge(1-d,((u<<1)|w)&mask,u>>shift)
                waiting[d][y].append((x,val))
                bits=edges[d].get(y,0)
                for e in (0,1):
                    if bits&(1<<e):pop(x,val,e)
    except (ValueError,OverflowError):return None
    return {'k':k,'left':sorted(edges[0].items()),'right':sorted(edges[1].items()),'states':sorted(seen)}

def domain_for(target):
    assert target in (1,7,8,9,10,11)
    return tuple((0,) if s==target else tuple(v for v in d if v>0) for s,d in enumerate(DOM))

def run_target(target):
    ds=domain_for(target)
    root=tuple(d[0] if len(d)==1 else -1 for d in ds)
    stack=[root];counts=Counter();mass=Counter();open_nodes=[];certs=[];halt_max=(0,None);start=time.monotonic()
    while stack:
        t=stack.pop();r=trace(t,128);typ=r[0];w=prod(len(ds[i]) for i,v in enumerate(t) if v<0)
        if typ in ('hole','open'):
            domain=tuple((v,) if v>=0 else ds[i] for i,v in enumerate(t))
            c=None
            for k in (1,2,3,4) if typ=='hole' else range(1,13):
                c=domain_check(domain,k,5000)
                if c is not None:break
            if c is not None:
                counts['abstract']+=1;mass['abstract']+=w;certs.append([t,c]);continue
        if typ=='hole':
            counts['split']+=1;s=r[2]
            stack.extend(t[:s]+(v,)+t[s+1:] for v in ds[s]);continue
        counts[typ]+=1;mass[typ]+=w
        if typ=='open':open_nodes.append(t)
        if typ=='halt' and r[1]+1>halt_max[0]:halt_max=(r[1]+1,t)
    assert sum(mass.values())==prod(map(len,ds))
    print('target',target,'counts',counts,'mass',mass,'maxhalt',halt_max,'seconds',time.monotonic()-start,flush=True)
    with open(f'target{target}.json','w') as f:
        json.dump({'target':target,'counts':counts,'mass':mass,'maxhalt':halt_max,'open':open_nodes,'certs':certs},f)

if __name__=='__main__':
    for i in map(int,sys.argv[1:]):run_target(i)
