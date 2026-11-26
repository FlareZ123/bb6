"""Finite push quotients with global symbol residues and tail run-class support.
The search constructs certificates; MaskBiDFA checks all edges and rows independently.
"""
from collections import defaultdict,deque

class AugDFA:
 def __init__(self,k,t0,p0,t1,p1,z,o,r,mask):
  self.k=k;self.threshold=(t0,t1);self.period=(p0,p1);self.mod=(z,o,r);self.mask=mask
  self.words=[((),0,0,0,0)];self.ids={self.words[0]:0};self.delta=[[-1,-1]]
 def push(self,s,b):
  if self.delta[s][b]>=0:return self.delta[s][b]
  pre,z,o,r,mask=self.words[s]
  if not pre and not b:self.delta[s][b]=0;return 0
  if b:o=(o+1)%self.mod[1]
  else:z=(z+1)%self.mod[0]
  if pre and pre[0][0]==b:
   n=pre[0][1]+1
   if n>=self.threshold[b]+self.period[b]:n=self.threshold[b]
   pre=((b,n),)+pre[1:]
  else:
   r=(r+1)%self.mod[2];pre=((b,1),)+pre
   if len(pre)>self.k:
    v,n=pre[-1];pre=pre[:-1]
    if self.mask:mask |= 1 << (v*32+(n if n<16 else 16+n%self.mask))
  new=(pre,z,o,r,mask)
  if new not in self.ids:self.ids[new]=len(self.words);self.words.append(new);self.delta.append([-1,-1])
  d=self.ids[new];self.delta[s][b]=d;return d
 def total(self):return [max(0,x) for row in self.delta for x in row]

def run_aug(table,params,cap=2000000):
 D=[AugDFA(*params[:9]),AugDFA(*params[9:])];T=table.replace('_','');T=[T[3*i:3*i+3] for i in range(12)];E=[defaultdict(dict),defaultdict(dict)];wait=[defaultdict(list),defaultdict(list)];seen={(0,0,0)};todo=deque(seen)
 for e in E:e[0][0,0]=None
 def add(s,l,r):
  x=(s,l,r)
  if x not in seen:seen.add(x);todo.append(x)
 def pop(st,b,prev):
  s,l,r=st;w,d,q=T[s];w=int(w);q=ord(q)-65
  if d=='R':add(2*q+b,D[0].push(l,w),prev)
  else:add(2*q+b,prev,D[1].push(r,w))
 while todo:
  if len(seen)>cap:return None,len(seen),'cap'
  st=todo.popleft();s,l,r=st;w,d,q=T[s]
  if w=='-':return None,len(seen),'hole'
  w=int(w);d=int(d=='R');src=l if d else r;dst=D[1-d].push(src,w);e=(w,src)
  if e not in E[1-d][dst]:
   E[1-d][dst][e]=None
   for v in wait[1-d][dst]:pop(v,*e)
  x=r if d else l;wait[d][x].append(st)
  for b,y in E[d][x]:pop(st,b,y)
 return [d.total() for d in D],len(seen),(E,seen)

SPECS={
 148:((6,8,3,8,3,2,2,1,0)*2,(7001,366,542,972)),
 265:((4,12,6,12,6,1,1,1,3)*2,(5894,126,630,818)),
}
def emit(rows,out):
 from emit_mask import emit_data
 for i,(params,expected) in SPECS.items():
  D,n,(E,S)=run_aug(rows[i],params)
  assert (n,len(D[0])//2,len(D[1])//2,sum(len(v) for e in E for v in e.values()))==expected
  emit_data(out,f'Raw54OneRAAug{i}',rows[i],D,E,S)
