"""Greedily quotient safe finite summaries with full closure rechecking."""
import sys,json,random,time
from regex_to_dfa import inv

def merge(D,i,j):
 p=list(range(len(D)))
 def root(a):
  while p[a]!=a:p[a]=p[p[a]];a=p[a]
  return a
 todo=[(i,j)]
 while todo:
  a,b=map(root,todo.pop())
  if a==b:continue
  if a>b:a,b=b,a
  p[b]=a;todo.extend(zip(D[a],D[b]))
 ids={root(0):0};todo=[root(0)];T=[]
 for q in todo:
  ds=[]
  for a in D[q]:
   a=root(a)
   if a not in ids:ids[a]=len(ids);todo.append(a)
   ds.append(ids[a])
  T.append(tuple(ds))
 return T

def reduce(t,L,R,seconds=10,seed=0):
 rng=random.Random(seed);start=time.monotonic();last=0;side=0
 while time.monotonic()-start<seconds and last<2:
  A,B=(L,R) if side==0 else(R,L)
  pairs=[(i,j) for i in range(len(A)) for j in range(i+1,len(A))]
  rng.shuffle(pairs);pairs.sort(key=lambda ij:sum(a==b for a,b in zip(A[ij[0]],A[ij[1]])),reverse=True)
  best=None
  for i,j in pairs:
   if time.monotonic()-start>=seconds:break
   Q=merge(A,i,j)
   if not Q or len(Q)>=len(A):continue
   I=inv(t,Q,B) if side==0 else inv(t,B,Q)
   if I:
    if side==0:L=Q
    else:R=Q
    best=Q;break
  if best:last=0
  else:last+=1
  side=1-side
 return L,R,inv(t,L,R)

if __name__=='__main__':
 from concurrent.futures import ProcessPoolExecutor
 def job(row):
  i,t,L,R,I,stat=row
  if not I:return row
  a,b,c=reduce(t,list(map(tuple,L)),list(map(tuple,R)),seconds=15)
  return [i,t,a,b,c,[len(L),len(R),len(I)]]
 with ProcessPoolExecutor(max_workers=3) as ex:
  for row in ex.map(job,map(json.loads,open(sys.argv[1]))):print(json.dumps(row),flush=True)
