from collections import defaultdict
from pathlib import Path
import json,glob,sys,time,heapq
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE.parent/'agent13-raw10-box15'),str(HERE.parent/'agent13-raw10-box17')]
from search_box15 import domain_check
from lag_rle import run
ALL=(1<<25)-1
BASE=[1<<v for v in [8,14,11,7,17,4]]+[ALL^(1<<9)]+[ALL]*5
def domain_mask(t):return tuple(1<<v if v>=0 else BASE[i]&~1 for i,v in enumerate(t))
def mask_domain(mask):return tuple(tuple(v for v in range(25) if m>>v&1) for m in mask)
def subset(a,b):return all(x&~y==0 for x,y in zip(a,b))
def convert(c):
 k=c['k'];mask=(1<<k)-1;S=[tuple(x) for x in c['states']];E=[];P=[];maps=[]
 for d in (0,1):
  ed=dict(c['left' if d==0 else 'right']);nodes={0}|{x[d+1] for x in S}|set(ed)
  for x in list(nodes):
   for b in (0,1):
    if ed.get(x,0)&(1<<b):nodes.add((x>>1)|(b<<(k-1)))
  nodes=sorted(nodes);ids={x:i for i,x in enumerate(nodes)};maps.append(ids)
  E.append([[(x&1,ids[(x>>1)|(b<<(k-1))]) for b in (0,1) if ed.get(x,0)&(1<<b)] for x in nodes]);P.append([[ids.get(((x<<1)|w)&mask,0) for w in (0,1)] for x in nodes])
 return {'edges':E,'pushes':P,'states':[(s,maps[0][l],maps[1][r]) for s,l,r in S]}
def compress(c):
 S={tuple(x) for x in c['states']};E=[[set(map(tuple,es)) for es in side] for side in c['edges']];P=[list(map(list,side)) for side in c['pushes']]
 while True:
  prev=tuple(map(len,E))
  for d in (0,1):
   inc=[set() for _ in E[d]]
   for s,l,r in S:
    z=(l,r);inc[z[d]].add((s,z[1-d]))
   groups={};phi=[];reps=[]
   for i,x in enumerate(inc):
    key=frozenset(x)
    if key not in groups:groups[key]=len(reps);reps.append(i)
    phi.append(groups[key])
   if len(reps)==len(phi):continue
   es=[set() for _ in reps]
   for i,e in enumerate(E[d]):
    for b,j in e:es[phi[i]].add((b,phi[j]))
   E[d]=es;P[d]=[[phi[j] for j in P[d][i]] for i in reps];S={(s,phi[l] if d==0 else l,phi[r] if d==1 else r) for s,l,r in S}
  if prev==tuple(map(len,E)):break
 return {'edges':[[sorted(es) for es in side] for side in E],'pushes':P,'states':sorted(S)}
def safe_mask(c):
 S={tuple(x) for x in c['states']};E=[[set(map(tuple,x)) for x in side] for side in c['edges']];P=c['pushes'];assert (0,0,0) in S and all((0,0) in side[0] for side in E)
 out=BASE[:]
 for s,l,r in S:
  out[s]&=~1;allowed=out[s]
  while allowed:
   low=allowed&-allowed;allowed^=low;v=low.bit_length()-1;q=(v-1)//4;w=(v-1)//2%2;d=1-(v-1)%2;z=[l,r];u=z[d];j=P[d][u][w]
   if (w,u) not in E[d][j]:out[s]&=~low;continue
   for b,k in E[1-d][z[1-d]]:
    ns=z[:];ns[d]=j;ns[1-d]=k
    if (2*q+b,*ns) not in S:out[s]&=~low;break
 return tuple(out)
def cert(t,param):
 if param[0]=='n':return convert(domain_check(mask_domain(domain_mask(t)),param[1],20000))
 if param[0]=='r':return run(t,param[1],max(2500,param[2]))
 raise ValueError(param)
def collect(target=None):
 allc=[]
 for f in sorted(glob.glob('ngram*.txt')):
  for l in open(f):
   a=list(map(int,l.split()));allc.append((tuple(a[:12]),('n',a[12]),a[13]))
 for f in sorted(glob.glob('long*.json')):
  for t,r in json.load(open(f))['out']:
   if r[0]=='rle':allc.append((tuple(t),('r',(r[1],r[1]),max(2500,r[2])),r[2]))
 for t,p,q in json.load(open(HERE/'survivors.json'))['stack']:
  if target is not None and t[target]!=0:continue
  cap=12000  # wide RLE classifier admits up to 10000 states
  c=run(t,(p,q),cap);assert c is not None, (t,p,q,cap)
  allc.append((tuple(t),('r',(p,q),cap),len(c['states'])))
 return allc
def main():
 target=int(sys.argv[1]) if len(sys.argv)>1 else None
 allc=collect(target);allc.sort(key=lambda x:x[0]);masks=[domain_mask(t) for t,_,_ in allc];N=len(allc);idx=[defaultdict(int) for _ in range(12)]
 for i,m in enumerate(masks):
  for j,v in enumerate(m):idx[j][v]|=1<<i
 full=(1<<N)-1;options=[];seen=set();start=time.monotonic()
 for i,(t,p,sz) in enumerate(allc):
  c=cert(t,p);assert c is not None
  c=compress(c);b=safe_mask(c);assert subset(masks[i],b)
  if b in seen:continue
  seen.add(b);cov=full
  for j,v in enumerate(b):
   allowed=0
   for m,ids in idx[j].items():
    if m&~v==0:allowed|=ids
   cov&=allowed
   if not cov:break
  options.append((i,b,cov,len(c['states'])))
 h=[(-cv.bit_count(),sz,i,j) for j,(i,b,cv,sz) in enumerate(options)];heapq.heapify(h);chosen=[];remaining=full
 while remaining:
  if not h:raise ValueError('not covered')
  old,sz,i,j=heapq.heappop(h);ii,b,cv,sz=options[j];c=cv&remaining;n=c.bit_count()
  if n==0:continue
  if -old!=n:heapq.heappush(h,(-n,sz,i,j));continue
  chosen.append((i,b,cv,sz));remaining^=c
 out=[{'t':allc[i][0],'param':allc[i][1],'mask':b,'states':sz} for i,b,cv,sz in chosen]
 json.dump({'boxes':out,'total':N},open('greedyboxes.json','w'))
 with open('greedyboxes.txt','w') as f:
  for x in out:f.write(' '.join(map(str,x['mask']))+'\n')
 print('chosen',len(chosen),'of',N,'stack candidates; states',sum(x['states'] for x in out),'seconds',time.monotonic()-start,flush=True)
if __name__=='__main__':main()
