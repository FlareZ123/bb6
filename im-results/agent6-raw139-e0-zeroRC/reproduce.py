"""Untrusted candidate census. Run from the repository root; Python 3 and g++.
Produces the same 590,963-leaf full ordinary-move partition as the local run.
The search outputs are not a formal Cover certificate.
"""
import pathlib, subprocess, json, hashlib
from collections import Counter
from functools import lru_cache
from collections import defaultdict, deque
from multiprocessing import Pool
from itertools import product
ROOT=pathlib.Path(__file__).resolve().parents[2]
WORK=pathlib.Path(__file__).resolve().parent
PARENT=[7,24,11,24,14,24,24,16,9,11,24,24]
def partition():
    s=(ROOT/'im-results/agent48-raw139-e0-0re/replay.cpp').read_text()
    s=s.replace('for(int i=t-1;i>=0;i--)','for(int i=t-1;i>=max(0,t-120);i--)')
    s=s.replace('if((a.b[C/64]^b.b[C/64]) && i<C/64)return false;','')
    s=s.replace('if((a.b[C/64]^b.b[C/64]) && i>C/64)return false;','')
    cpp=WORK/'partition.cpp';cpp.write_text(s)
    exe=WORK/'partition'; subprocess.run(['g++','-O3','-std=c++17',str(cpp),'-o',str(exe)],check=True)
    out=WORK/'partition.json'
    with out.open('wb') as f:
        subprocess.run([str(exe),'250','2',*map(str,PARENT)],stdout=f,check=True)
    p=json.loads(out.read_text())
    assert p['counts']==dict(cycle=396176,last=131349,split=25694,far=54205,open=9233,maxquery=249)
    print('Partition SHA256:',hashlib.sha256(out.read_bytes()).hexdigest(),flush=True)
    return p

def generate(table,width=2,cap=1,mod=1,runs=1,flip=False,event_limit=10000,phase=False):
    """Agent48 block-FAR saturation, skipping proof-data minimization."""
    alphabet=2**width
    moves=[None if n==24 else ((n>>1)&1,bool(n&1)!=flip,n>>2) for n in table]
    @lru_cache(None)
    def macro(q,d,a):
        h=0 if d else width-1; seen=set()
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
        elif phase:ys=((a,)+xs[0][:runs-1] if xs else (a,), ((xs[1] if xs else 0)+1)%mod)
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
    return len(left),len(nodes),count

PARAMS=[(2,1,1,1,False,False),(3,1,1,1,False,False),(2,1,1,2,False,True),(2,1,2,1,False,False),(2,1,1,2,False,False),(2,1,3,2,False,False),(3,1,2,2,False,False),(2,1,3,1,False,False),(2,1,5,2,False,False),(2,1,2,2,False,False),(2,1,3,4,False,False),(3,1,1,2,False,False),(2,1,3,3,False,True)]
MORE=[(1,1,1,False),(1,2,1,False),(1,3,1,False),(1,1,2,False),(1,2,2,False),(1,3,2,False),(1,4,2,False),(1,5,2,False),(1,6,2,False),(1,7,2,False),(2,2,2,False),(1,1,3,False),(1,2,3,False),(1,3,3,False),(1,4,3,False),(1,5,3,False),(1,1,4,False),(1,2,4,False),(1,3,4,False)]+[(1,m,r,True) for r in [2,3,4] for m in range(1,8)]
def replay(p,limit):
    q=h=0;tape=set()
    for n in range(limit+1):
        s=2*q+(h in tape);v=p[s]
        if v==24:return n,s
        if v&2:tape.add(h)
        else:tape.discard(h)
        h+=1 if v&1 else -1;q=v>>2
    return None
def scan(p,cap=2000):
    q=h=t=0;history=[]
    for n in range(cap+1):
        s=2*q+((t>>(h+cap))&1);v=p[s]
        if v==24:return ('late',n,s)
        lo=hi=h
        for i in range(n-1,max(-1,n-101),-1):
            oq,oh,ot=history[i];lo=min(lo,oh);hi=max(hi,oh)
            if oq!=q:continue
            d=h-oh
            if d>=0 and ot>>(lo+cap)==t>>(lo+cap+d):return ('cycle',i,n-i,1,lo)
            if d<=0 and ot&((1<<(hi+cap+1))-1)==(t&((1<<(hi+cap+d+1))-1))<<(-d):return ('cycle',i,n-i,0,hi)
        history.append((q,h,t));t=(t&~(1<<(h+cap)))|(((v>>1)&1)<<(h+cap));h+=1 if v&1 else -1;q=v//4
    return ('open',)
def basic(job):
    i,t=job
    for params in PARAMS:
        r=generate(t,*params[:-1],phase=params[-1])
        if r:return i,['block',*params,*r]
    return i,['open']
def hard(job):
    i,t=job;r=scan(t)
    if r[0]!='open':return i,list(r)
    for flip,w,(cap,mod,runs,phase) in product([False,True],[2,3,4],MORE):
        params=(w,cap,mod,runs,flip,phase)
        r=generate(t,*params[:-1],phase=phase,event_limit=50000)
        if r:return i,['block',*params,*r]
    r=replay(t,200000)
    return (i,['late',*r]) if r else (i,['open'])
def child(job):
    i,r=basic(job)
    return hard(job) if r[0]=='open' else (i,r)
def run():
    p=partition();ts=p['open']
    with Pool(4) as pool:
        recipes=dict(pool.imap_unordered(basic,enumerate(ts),chunksize=16))
        print('Basic:',Counter(r[0] for r in recipes.values()),flush=True)
        recipes.update(pool.imap_unordered(hard,[(i,ts[i]) for i,r in recipes.items() if r[0]=='open']))
        print('Hard:',Counter(r[0] for r in recipes.values()),flush=True)
        assert [i for i,r in recipes.items() if r[0]=='open']==[5144]
        assert ts[5144]==[7,23,11,7,14,1,6,16,9,11,24,19]
        assert replay(ts[5144],1673357)==(1673357,10)
        recipes[5144]=['late',1673357,10]
        jobs=[]
        for i,v in sorted(recipes.items()):
            if v[0]=='late' and ts[i].count(24)>1:
                for a in range(24):
                    u=ts[i].copy();u[v[2]]=a;jobs.append(((i,a),u))
        assert len(jobs)==96
        children=dict(pool.imap_unordered(child,jobs))
        assert all(r[0]!='open' for r in children.values())
        print('Children:',Counter(r[0] for r in children.values()),flush=True)
    (WORK/'recipes.jsonl').write_text(''.join(json.dumps([i,r])+'\n' for i,r in sorted(recipes.items())))
    (WORK/'children.jsonl').write_text(''.join(json.dumps([i,r])+'\n' for i,r in sorted(children.items())))
if __name__=='__main__':run()
