"""Exact run-length B0 return map for 1RB0RD_1LC1LB_0LE0LC_1RF1LE_1RE0RA_1LB---.
W: run lengths of ones beyond first two zeros on left (single zero separators).
R: leading one-run length, then alternating positive finite zero/one-run lengths.
Terminal blank tails implicit. Steps count includes final halt. F counts successful F0.
"""
from collections import deque
from dataclasses import dataclass
class W:
 def __init__(self,runs=()):
  self.d=deque();n=0
  for s in runs:
   if s==1:n+=1
   else:self.d.append((n,s));n=0
  if n:self.d.append((n-1,1))
 def __bool__(self):return bool(self.d)
 def push(self,k,s):
  if s==1 and self.d:
   n,v=self.d.popleft();self.d.appendleft((k+1+n,v))
  else:self.d.appendleft((k,s))
 def pop(self):
  k,s=self.d.popleft()
  if k:self.d.appendleft((k-1,s));return 1
  return s
 def prefix(self):return self.d[0][0] if self.d else 0
 def expand(self):return [x for k,v in self.d for x in [1]*k+[v]]
 def __repr__(self):return str(list(self.d))

def addones(r,n):return [r[0]+n,*r[1:]]
def addgap(r,n):
 assert n>0 and r[0]>0
 return [0,n,*r]
def cutgap(r):
 if len(r)==1:return [0]
 g=r[1];assert g>=2
 return r[2:] if g==2 else [0,g-2,*r[2:]]

@dataclass
class Result:
 a: int
 w: W
 r: list
 steps: int
 f: int
 returns: int=1
 halt: bool=False

def y(a,w,r,accelerate=True):
 b=r[0];g=r[1] if len(r)>1 else 0
 if accelerate and a==1 and b%2 and len(r)==1 and w.prefix()>=3:
  k,s=w.d.popleft();n=k//3;w.d.appendleft((k-3*n,s))
  return Result(a,w,[b+8*n],n*(5*b+47)+20*n*(n-1),n,2*n)
 u=w.pop() if w else 0;s=a+2+u
 if b%2:
  if g==1:return Result(a,w,r,2*a+2*b+6,0,halt=True)
  R=addones(cutgap(r),b+3);steps=2*a+2*b+7+3*(b+1)
  if not w:return Result(s-1,w,R,steps,1)
  v=w.pop();R=addones(addgap(addones(R,1),s-2),v-1)
  return Result(1,w,R,steps+s+3+5*(v-1),1)
 k=b//2
 if g!=1:
  R=cutgap(r);steps=2*a+2*b+6
  if k:w.push(k-1,s);return Result(1,w,addones(R,1),steps+5,0)
  return Result(1,w,addones(R,s),steps+5*s,0)
 R=addones(r[2:],1);steps=2*a+2*b+8
 if k>=2:w.push(k-2,s);return Result(1,w,addones(R,1),steps+5,0)
 if k==1:return Result(1,w,addones(R,s),steps+5*s,0)
 if not w:return Result(s,w,R,steps,0)
 v=w.pop();R=addones(addgap(addones(R,1),s-1),v-1)
 return Result(1,w,R,steps+s+4+5*(v-1),0)

def encode_runs(rs,bit=1):
 out=0;shift=0
 for n in rs:
  if bit:out|=((1<<n)-1)<<shift
  shift+=n;bit^=1
 return out

def encode_y(a,ws,rs):
 lr=[a,2]
 for s in ws:lr.extend([s,1])
 return encode_runs(lr),encode_runs(rs)

def primitive_y(l,r,t):
 q=1;r<<=1;n=f=0
 while True:
  v=t[2*q+(r&1)];n+=1
  if not v:return None,None,n,f
  if q==5:f+=1
  v-=1;w=v//2%2
  if v%2:l=(l<<1)|w;r>>=1
  else:r=(((r>>1)<<1)|w)<<1|(l&1);l>>=1
  q=v//4
  if q==1 and not r&1:
   a=(l^(l+1)).bit_length()-1
   if not (l>>(a+1))&1:return l,r>>1,n,f

def test():
 import random
 rng=random.Random(13)
 t=[8,14,11,7,17,9,24,19,20,2,7,0]
 t0=[8,14,11,7,17,9,22,19,20,2,3,0]
 for _ in range(5000):
  a=rng.randrange(1,9);ws=[rng.randrange(1,6) for _ in range(rng.randrange(5))];rs=[rng.randrange(12)]+[rng.randrange(1,6) for _ in range(2*rng.randrange(5))]
  l,r=encode_y(a,ws,rs);v=y(a,W(ws),rs,False)
  p=primitive_y(l,r,t);p0=primitive_y(l,r,t0)
  if v.halt:assert p[:2]==(None,None) and p[2:]==(v.steps,v.f),(a,ws,rs,v,p)
  else:assert p==(*encode_y(v.a,v.w.expand(),v.r),v.steps,v.f),(a,ws,rs,v,p)
  assert p0[:2]==p[:2] and p0[2]==p[2]+2*p[3] and p0[3]==p[3],(a,ws,rs,p,p0)
 for b in range(1,32,2):
  for k in range(3,30):
   ws=[1]*k+[4,3];a=1;r=[b];v=y(a,W(ws),r,True);w=W(ws);s=f=0
   for _ in range(v.returns):
    z=y(a,w,r,False);a,w,r=z.a,z.w,z.r;s+=z.steps;f+=z.f
   assert (a,w.expand(),r,s,f)==(v.a,v.w.expand(),v.r,v.steps,v.f)
 print('5000 arbitrary Y configurations agree for both machines; accelerated sums agree',flush=True)

if __name__=='__main__':
 test();a,w,r=1,W(),[0];n=1;f=0;returns=0;seen=set();trace=[]
 for i in range(1000000):
  key=(a,tuple(w.d),tuple(r));assert key not in seen,('cycle',i);seen.add(key)
  v=y(a,w,r);n+=v.steps;f+=v.f;returns+=v.returns
  trace.append({'index':i,'a':a,'W':list(key[1]),'R':list(key[2]),'steps':v.steps,'f':v.f,'returns':v.returns,'halt':v.halt})
  if v.halt:
   print('HALT short',n,'long',n+2*f,'F0',f,'Y returns',returns,'compressed',i+1,'configuration',key,flush=True)
   import json;json.dump(trace,open('halt_trace.json','w'),indent=2)
   assert (n,n+2*f,f,returns,i+1)==(3142249302385140,3142249368711030,33162945,66325897,214)
   break
  a,w,r=v.a,v.w,v.r
  if max(a,*r).bit_length()>5000:raise RuntimeError('bit budget exceeded')
 else:raise RuntimeError('no halt in loop')
