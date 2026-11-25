from dataclasses import dataclass
from itertools import product
from collections import defaultdict
import json, sys
@dataclass(frozen=True)
class G:
 p:str

def normalize(xs):
 out=[]
 for x in xs:
  if not x:continue
  if isinstance(x,str) and out and isinstance(out[-1],str):out[-1]+=x
  else:out.append(x)
 return tuple(out)
def front(x):return x[0] if x and isinstance(x[0],str) else ''
def split(x,k):
 a=front(x);assert len(a)>=k
 return a[:k],normalize([a[k:],*x[1:]]) if a else x

def cons(s,x):return normalize((s,*x))
def pop(x):
 if not x:return '0',()
 if not isinstance(x[0],str):raise ValueError('unknown')
 return x[0][0],normalize((x[0][1:],*x[1:]))
def step(p,c):
 q,l,r=c
 try:b,L=pop(l)
 except ValueError:return None
 v=p[2*q+int(b)]
 if v==24:return None
 w=str((v>>1)&1);a=v>>2
 if v&1:
  try:b,R=pop(r)
  except ValueError:return None
  return a,cons(b+w,L),R
 return a,L,cons(w,r)
def trace(p,lim):
 c=(0,(),());out=[c]
 for _ in range(lim):
  c=step(p,c)
  if c is None:break
  out.append(c)
 return out

def lit(xs):return ''.join(xs)
def evaluate(c,n):return c[0],''.join(x if isinstance(x,str) else x.p*n for x in c[1]),''.join(x if isinstance(x,str) else x.p*n for x in c[2])

def insertions(s,t):
 d=len(t)-len(s)
 if d<0 or d>20:return []
 if d==0:return [()] if s==t else []
 return [(i,t[i:i+d]) for i in range(len(s)+1) if s[:i]==t[:i] and s[i:]==t[i+d:]]
def form(s,ins):
 if not ins:return normalize([s])
 i,p=ins;return normalize([s[:i],G(p),s[i:]])

def canonical(x):
 out=list(x)
 for i in range(len(out)):
  if not isinstance(out[i],G):continue
  P=out[i].p
  if i and isinstance(out[i-1],str):
   s=out[i-1];m=''
   while s and s[-1]==P[-1]:
    b=s[-1];s=s[:-1];P=b+P[:-1];m=b+m
   out[i-1]=s;out[i]=G(P)
   if m:
    if i+1<len(out) and isinstance(out[i+1],str):out[i+1]=m+out[i+1]
    else:out.insert(i+1,m)
 return normalize(out)

def pump(p,c,side):
 q,l,r=c; source,dest=(l,r) if side=='L' else (r,l)
 sp=front(source);idx=1 if sp else 0
 if idx>=len(source) or not isinstance(source[idx],G):return []
 P=source[idx].p;sr=source[idx+1:];dp=front(dest)
 out=[]
 # A and B are opaque tails: step refuses to read them.
 for j in range(min(len(dp),24)+1):
  dpre,drest=split(dest,j)
  A=G('L');B=G('R')
  ls=normalize([sp,P,A]);rs=normalize([dpre,B]);
  if side=='R':ls,rs=rs,ls
  a=(q,ls,rs)
  for k in range(1,161):
   a=step(p,a)
   if a is None:break
   if a[0]!=q:continue
   s,d=(a[1],a[2]) if side=='L' else (a[2],a[1]);
   if s!=normalize([sp,A]):continue
   if not d or d[-1]!=B:continue
   if len(d)>2 or (len(d)==2 and not isinstance(d[0],str)):continue
   w=front(d)
   if not w.startswith(dpre):continue
   O=w[len(dpre):];
   D=normalize([dpre,*([G(O)] if O else []),*drest]);S=normalize([sp,*sr]);
   b=(q,S,D) if side=='L' else (q,D,S)
   out.append((b,(side,q,sp,dpre,P,O,k,sr,drest)))
   break
 return out

def targetnext(c):
 def nextword(w):return normalize([y for x in w for y in ((x,) if isinstance(x,str) else (x.p,x))])
 return c[0],nextword(c[1]),nextword(c[2])

def solve(p,c,target,maxsteps=500):
 stack=[(c,[],0,0)];seen=set()
 while stack:
  a,ops,steps,cost=stack.pop()
  if ops and a[0]==target[0] and canonical(a[1])==canonical(target[1]) and canonical(a[2])==canonical(target[2]):return ops,a
  if steps>maxsteps or len(ops)>maxsteps or a in seen:continue
  if sum(len(x) if isinstance(x,str) else len(x.p) for w in a[1:] for x in w)>200:continue
  seen.add(a)
  b=step(p,a)
  if b is not None:stack.append((b,ops+[('step',a,b)],steps+1,cost+1))
  for side in ('L','R'):
   for b,op in pump(p,a,side):stack.append((b,ops+[('pump',a,b,op)],steps+1,cost))
  if len(seen)>10000:break
 return None

def candidates(tr):
 cs=[evaluate(c,0) for c in tr]; inds=defaultdict(list)
 for i,c in enumerate(cs):inds[c].append(i)
 for i,c in sorted(enumerate(cs[:400]),key=lambda x:(min(map(len,x[1][1:])),sum(map(len,x[1][1:])),x[0])):
  q,l,r=c
  for j in range(i+1,min(len(cs),i+500)):
   s,m,n=cs[j]
   if s!=q or len(m)+len(n)<=len(l)+len(r):continue
   ls=insertions(l,m);rs=insertions(r,n)
   if not ls or not rs:continue
   for il,ir in product(ls,rs):
    a=(q,form(l,il),form(r,ir));e=evaluate(a,2);ks=inds.get(e,[])
    if not any(k>j for k in ks):continue
    yield i,j,a

def find(p,lim=2000):
 tr=trace(p,lim);seen=set();attempts=0
 for i,j,a in candidates(tr):
  key=(a[0],canonical(a[1]),canonical(a[2]));
  if key in seen:continue
  seen.add(key);attempts+=1
  if attempts>250:break
  sol=solve(p,a,targetnext(a),150)
  if sol:return i,a,sol
 return None

def js(v):
 if isinstance(v,G):return {'g':v.p}
 raise TypeError
