"""Regular-language widening exploration of two independent tape rays.

Candidate invariants only; regex_to_dfa.py rechecks finite abstract
reachability, and RegularRayInvariant.lean is the independent proof gate.
"""
from functools import lru_cache
from collections import deque,defaultdict
import sys,json,time,itertools
@lru_cache(maxsize=100000)
def normalize(p):
 out=[]
 for w,s in p:
  if not w:continue
  if not s and out and not out[-1][1]:out[-1]=(out[-1][0]+w,False)
  elif s and out and out[-1]==(w,True):continue
  else:out.append((w,s))
 return tuple(out)

def concat(*args):return normalize(tuple(itertools.chain.from_iterable(args)))
def fixed(w):return ((w,False),) if w else ()
@lru_cache(maxsize=100000)
def pops(p):
 if not p:return (('0',()),)
 (w,s),*rest=p;rest=tuple(rest)
 if not s:return ((w[0],concat(fixed(w[1:]),rest)),)
 return tuple(dict.fromkeys(((w[0],concat(fixed(w[1:]),p)),)+pops(rest)))

@lru_cache(maxsize=50000)
def nfa(p):
 E=[{} for _ in range(1+sum(len(w) for w,s in p))];S=[[] for _ in E];at=0
 for w,s in p:
  k=at
  for b in w:
   E[at][b]=at+1;at+=1
  if s:
   E[at-1][w[-1]]=k;S[k].append(at)
 C=[]
 for i in range(len(E)):
  v=1<<i;stack=[i]
  while stack:
   j=stack.pop()
   for k in S[j]:
    if not v>>k&1:v|=1<<k;stack.append(k)
  C.append(v)
 T=tuple(tuple(C[e[b]] if b in e else 0 for b in '01') for e in E)
 return (C[0],1<<at,T)

@lru_cache(maxsize=200000)
def subset(p,q):
 if p==q:return True
 a,af,A=nfa(p);b,bf,B=nfa(q)
 def next(v,T,c):
  z=0
  while v:
   w=v&-v;v-=w;z|=T[w.bit_length()-1][c]
  return z
 todo=[(a,b)];seen={(a,b)}
 while todo:
  a,b=todo.pop()
  if a&af and not b&bf:return False
  for c in (0,1):
   aa=next(a,A,c);bb=next(b,B,c)
   if aa and (aa,bb) not in seen:seen.add((aa,bb));todo.append((aa,bb))
 return True

@lru_cache(maxsize=200000)
def widen(p,threshold,retain,maxword):
 out=[]
 for w,s in p:
  if s:out.append((w,s));continue
  k=0;last=0
  while k<len(w):
   best=None
   for m in range(1,min(maxword,(len(w)-k)//threshold)+1):
    block=w[k:k+m];n=1
    while w.startswith(block,k+n*m):n+=1
    if n>=threshold and (best is None or n*m>best[0]*best[1]):best=(m,n,block)
   if best is None:k+=1;continue
   m,n,b=best
   if k>last:out.append((w[last:k],False))
   out.extend([(b*retain,False),(b,True)])
   k+=m*n;last=k
  if last<len(w):out.append((w[last:],False))
 return normalize(tuple(out))

def succs(p,z):
 q,l,r=z;out=[]
 for a,L in pops(l):
  t=p[2*q+int(a)]
  if t=='---':return None
  w,d,nq=t;nq=ord(nq)-65
  if d=='L':out.append((nq,L,concat(fixed(w),r)))
  else:
   for b,R in pops(r):out.append((nq,concat(fixed(b+w),L),R))
 return out

def solve(table,threshold=4,retain=1,maxword=8,limit=3000,timeout=2):
 s=table.replace('_','');p=[s[i:i+3] for i in range(0,36,3)];start=(0,(),());todo=deque([start]);Q=defaultdict(list);Q[0].append(((),()));ct=0;now=time.monotonic()
 def incl(z,w):return subset(z[0],w[0]) and subset(z[1],w[1])
 while todo:
  if ct>=limit or time.monotonic()-now>timeout:return None,('limit',ct,len(todo))
  z=todo.popleft();q,l,r=z;ct+=1
  if (l,r) not in Q[q]:continue
  xs=succs(p,z)
  if xs is None:return None,('halt',ct,z)
  for nq,nl,nr in xs:
   v=(nl,nr);A=Q[nq]
   if any(incl(v,w) for w in A):continue
   v=(widen(nl,threshold,retain,maxword),widen(nr,threshold,retain,maxword))
   if any(incl(v,w) for w in A):continue
   A[:]=[w for w in A if not incl(w,v)];A.append(v);todo.append((nq,*v))
 return [[q,l,r] for q,rs in Q.items() for l,r in rs],('success',ct)

if __name__=='__main__':
 from concurrent.futures import ProcessPoolExecutor
 def task(row):
  i,t=row.split();res=None;last=None
  for th,ret,mw in [(3,0,8),(3,1,8),(4,1,8),(4,2,8),(5,2,12),(6,3,12)]:
   res,last=solve(t,th,ret,mw,limit=3000,timeout=2)
   if res:return [i,t,th,ret,mw,res,last]
  return [i,t,None,None,None,None,last]
 with ProcessPoolExecutor(max_workers=4) as ex:
  for r in ex.map(task,[x for x in open(sys.argv[1]) if x.strip()]):
   print(json.dumps(r),flush=True)
