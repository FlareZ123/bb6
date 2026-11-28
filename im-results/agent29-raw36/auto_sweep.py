"""Find an affine sweep recurrence from repeated concrete zipper shapes.
Candidates require four exact snapshots, then an opaque-tail symbolic proof.
The output is a recipe; only the original Lean kernel is authoritative.
"""
import collections,itertools,json,sys
import discover_sweep as ds
from concurrent.futures import ProcessPoolExecutor

def solve(p,start,c0,c1,maxnodes=4000):
    goal=(start[0],*[[x+(a[j+1] if j+1<len(a) else '') if j%2==0 else x for j,x in enumerate(a)] for a in start[1:]])
    key=lambda z:(z[0],tuple(z[1]),tuple(z[2]))
    dq=collections.deque([(start,[],0,0)])
    seen={(key(start),0,0)}
    while dq and len(seen)<=maxnodes:
        z,act,t0,t1=dq.popleft()
        if t0==c0 and t1==c1:
            if ds.same(z,goal):
                out=[]
                for x in act:
                    if isinstance(x,int) and out and isinstance(out[-1],int):out[-1]+=x
                    else:out.append(x)
                return out
            continue
        if t1<c1:
            for a,znew in ds.options(p,z,min(100,c1-t1)):
                k=(key(znew),t0,t1+a[-1])
                if k not in seen:seen.add(k);dq.append((znew,act+[a],t0,t1+a[-1]))
        if t0<c0:
            try:znew=ds.em.step(p,z)
            except (AssertionError,ValueError):continue
            k=(key(znew),t0+1,t1)
            if k not in seen:seen.add(k);dq.append((znew,act+[1],t0+1,t1))
    return None

def insertion(x,y):
    if x==y:return [[x]]
    d=len(y)-len(x)
    if not 0<d<=32:return []
    return [[x[:j],y[j:j+d],x[j:]] for j in range(len(x)+1) if y==x[:j]+y[j:j+d]+x[j:]]

def expand(a,n):return ''.join(x*(n if i%2 else 1) for i,x in enumerate(a))
def run(job):
    idx,s=job;s=s.replace('_','');p=[s[i:i+3] for i in range(0,36,3)];z=(0,'','');zs=[];by=collections.defaultdict(list);times={}
    for t in range(1801):
        zs.append(z);by[z[0]].append(t);times[z]=t
        try:z=ds.concrete_step(p,z)
        except ValueError:break
    trials=0;seen=set()
    for t0,a in enumerate(zs[:600]):
        if len(a[1])+len(a[2])>85:continue
        for t1 in by[a[0]]:
            if t1<=t0:continue
            if t1>t0+220:break
            b=zs[t1];d1=len(b[1])-len(a[1]);d2=len(b[2])-len(a[2])
            if min(d1,d2)<0 or not 0<d1+d2<=32:continue
            l=insertion(a[1],b[1]);r=insertion(a[2],b[2])
            if not l or not r:continue
            for ll,rr in itertools.product(l,r):
                c=(a[0],expand(ll,2),expand(rr,2));t2=times.get(c,-1)
                if t2<t1+(t1-t0):continue
                c0=t1-t0;c1=t2-t1-c0
                if not 0<c1<=220:continue
                t3=times.get((a[0],expand(ll,3),expand(rr,3)))
                if t3!=t2+c0+2*c1:continue
                k=(a[0],tuple(ll),tuple(rr),c0,c1)
                if k in seen:continue
                seen.add(k);trials+=1
                if trials>60:return None
                acts=solve(p,(a[0],ll,rr),c0,c1)
                if acts:
                    rec=[idx,s,t0,a[0],'|'.join(ll),'|'.join(rr),acts]
                    try:ds.em.emit(rec)
                    except AssertionError:continue
                    return rec
    return None
if __name__=='__main__':
    xs=[l.strip() for l in open(sys.argv[1]) if l.strip()]
    with ProcessPoolExecutor(max_workers=int(sys.argv[2])) as ex:
        for (i,s),rec in zip(enumerate(xs),ex.map(run,enumerate(xs),chunksize=1)):
            if rec: print(json.dumps(rec),flush=True)
            else:print('MISS',s,file=sys.stderr,flush=True)
