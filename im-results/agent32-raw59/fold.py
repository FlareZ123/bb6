"""Greedy deterministic congruence folding, with independent saturation after every candidate."""
from quotient_search import witness
from collections import defaultdict
import random,time

def partial(D,Es):
 out=[]
 for d in range(2):
  row=[-1]*len(D[d])
  for x,edges in Es[d].items():
   for b,y in edges:
    assert row[2*y+b] in (-1,x)
    row[2*y+b]=x
  out.append(row)
 return out

def fold(d,pair):
 n=len(d)//2;p=list(range(n));d=d[:];todo=[pair]
 def find(x):
  while p[x]!=x:p[x]=p[p[x]];x=p[x]
  return x
 while todo:
  x,y=map(find,todo.pop())
  if x==y:continue
  if x>y:x,y=y,x
  p[y]=x
  for b in (0,1):
   a,c=d[2*x+b],d[2*y+b]
   if a<0:d[2*x+b]=c
   elif c>=0:todo.append((a,c))
 roots=[i for i in range(n) if p[i]==i];ix={x:i for i,x in enumerate(roots)}
 return [ix[find(d[2*x+b])] if d[2*x+b]>=0 else 0 for x in roots for b in (0,1)]

def candidate_pairs(D,part,S,rng,cap=3000):
 P=[defaultdict(set),defaultdict(set)]
 for s,l,r in S:P[0][l].add((s,r));P[1][r].add((s,l))
 options=[]
 for k in range(2):
  for x in range(len(D[k])//2):
   for y in range(x):
    a,b=P[k][x],P[k][y]
    diff=len(a^b)/max(1,len(a|b)); sim=sum(part[k][2*x+i]==part[k][2*y+i] or min(part[k][2*x+i],part[k][2*y+i])<0 for i in (0,1))
    options.append((diff+0.12*(2-sim)+rng.random()*0.08,k,x,y))
 options.sort();return options[:cap]

def minimize(record,max_attempts=2000,seed=32,verbose=True):
 D=record['dfa'];table=record['table'];E,n,S=witness(table,D);assert E is not None
 p=partial(D,E);rng=random.Random(seed);start=time.monotonic();rounds=attempts=0
 while attempts<max_attempts:
  found=False;opts=candidate_pairs(D,p,S,rng)
  for score,k,x,y in opts:
   if attempts>=max_attempts:break
   attempts+=1;dd=fold(p[k],(x,y));D1=D[:];D1[k]=dd
   E1,n1,S1=witness(table,D1,cap=max(n*2,1000))
   if E1 is None or n1>n:continue
   D=D1;E,n,S=E1,n1,S1;p=partial(D,E);rounds+=1;found=True
   if verbose and rounds%5==0:print('merge',rounds,'attempts',attempts,'classes',len(D[0])//2,len(D[1])//2,'states',n,'time',round(time.monotonic()-start,2),flush=True)
   break
  if not found:break
 if verbose:print('final',rounds,'merges',attempts,'attempts','classes',len(D[0])//2,len(D[1])//2,'states',n,flush=True)
 return dict(table=table,dfa=D,states=n,edges=sum(len(v) for e in E for v in e.values()),method=record['method']+'+fold')
