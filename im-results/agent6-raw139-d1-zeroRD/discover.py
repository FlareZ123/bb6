#!/usr/bin/env python3
"""Untrusted deterministic witness discovery for the five residual traces.
The Lean checkers, not this script, establish the conclusions."""
from collections import Counter
from pathlib import Path
import json,sys

TABLES={
 3:[7,19,11,0,14,23,2,13,9,16,5,24],
 27:[7,16,11,9,14,1,2,13,20,24,8,15],
 77:[7,16,11,15,14,1,2,13,20,8,24,9],
 78:[7,16,11,15,14,1,2,13,22,8,24,2],
 335:[7,20,11,19,14,3,2,13,15,11,24,10],
}
def step(p,z,strict=False):
 q,L,R=z
 if strict and not L:return None
 v=p[2*q+(L[0]=='1' if L else 0)]
 if v==24:return None
 w=str((v>>1)&1);q=v//4
 if v&1:
  if strict and not R:return None
  return (q,(R[0] if R else '0')+w+L[1:],R[1:])
 return (q,L[1:],w+R)

def candidate(p,z,period=24):
 q,L,R=z;u=z;h=lo=hi=0;best=None;score=0
 for k in range(1,period+1):
  s=p[2*u[0]+(u[1][0]=='1' if u[1] else 0)]
  if s==24:break
  v=step(p,u);h+=1 if s&1 else -1;lo=min(lo,h);hi=max(hi,h);u=v
  if u[0]!=q or not h:continue
  ll=1-lo;rr=hi
  if len(L)<ll or len(R)<rr:continue
  if h<0:
   lp=L[:ll+h];rp=R[:rr];I=L[ll+h:ll];stream=L;offset=len(lp);side='left'
  else:
   lp=L[:ll];rp=R[:rr-h];I=R[rr-h:rr];stream=R;offset=len(rp);side='right'
  n=1
  while stream.startswith(I,offset+n*len(I)):n+=1
  if n<2 or k*n<=score or k*n<5:continue
  small=(q,L[:ll],R[:rr]);out=small
  for j in range(k):
   out=step(p,out,True)
   if out is None:break
  if not out or out[0]!=q:continue
  _,l,r=out
  if h<0:
   if l!=lp or not r.startswith(rp) or len(r)!=len(rp)+len(I):continue
   O=r[len(rp):];dest=(q,lp+L[len(lp)+n*len(I):],rp+O*n+R[len(rp):])
  else:
   if r!=rp or not l.startswith(lp) or len(l)!=len(lp)+len(I):continue
   O=l[len(lp):];dest=(q,lp+O*n+L[len(lp):],rp+R[len(rp)+n*len(I):])
  best=((side,lp,rp,I,O,k,n),dest);score=k*n
 return best

def compress(p,limit=10000000):
 z=(0,'','');t=0;actions=[];times=[];endpoints=[];raw=0;hist=Counter()
 while t<limit:
  nxt=step(p,z)
  if nxt is None:break
  m=candidate(p,z)
  if m is not None:
   if raw: actions.append(('raw',raw));times.append(t);endpoints.append(z);raw=0
   action,z=m;actions.append(action);t+=action[-1]*action[-2];times.append(t);endpoints.append(z);hist[action[:-1]]+=1
  else:
   z=nxt;t+=1;raw+=1
   if raw>=100:actions.append(('raw',raw));times.append(t);endpoints.append(z);raw=0
 if raw:actions.append(('raw',raw));times.append(t);endpoints.append(z)
 return {'codes':p,'t':t,'last':z,'actions':actions,'times':times,'endpoints':endpoints,'hist':[(k,v) for k,v in hist.most_common()]}

def compressSegment(p,z,tmax):
 t=0;acts=[];times=[];ends=[];raw=0
 while t<tmax:
  nxt=step(p,z);assert nxt is not None
  m=candidate(p,z)
  if m is not None and t+m[0][-1]*m[0][-2]<=tmax:
   if raw:acts.append(('raw',raw));times.append(t);ends.append(z);raw=0
   act,z=m;acts.append(act);t+=act[-1]*act[-2];times.append(t);ends.append(z)
  else:
   z=nxt;t+=1;raw+=1
   if raw>=100:acts.append(('raw',raw));times.append(t);ends.append(z);raw=0
 if raw:acts.append(('raw',raw));times.append(t);ends.append(z)
 return {'codes':p,'actions':acts,'times':times,'endpoints':ends,'last':z,'t':t}

if __name__=='__main__':
 for i in map(int,sys.argv[1:]):
  p=TABLES[i]
  if i in (77,78):
   entry,period={77:(32835,16333),78:(30903,15373)}[i]
   d=compressSegment(p,(0,'',''),entry);z=d['last']
   Path(f'cycle-entry-{i}.json').write_text(json.dumps(d))
   s=(z[0],z[1][:64],z[2]);c=compressSegment(p,s,period);c['start']=s
   Path(f'cycle-period-{i}.json').write_text(json.dumps(c))
   print(i,'entry actions',len(d['actions']),'period actions',len(c['actions']))
  else:
   assert i in (3,335), 'ID27 has no finite witness'
   d=compress(p);Path(f'compressed-{i}.json').write_text(json.dumps(d))
   print(i,'arrival',d['t'],d['last'][0],len(d['last'][1]),len(d['last'][2]),'actions',len(d['actions']))
