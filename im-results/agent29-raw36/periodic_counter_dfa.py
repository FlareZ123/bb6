"""Test exact two-ray abstraction from periodic digit-position masks."""
from regex_to_dfa import inv
import json,time,sys

def build(start,step,limit=50000):
 ids={start:0};todo=[start];D=[]
 for a in todo:
  out=[]
  for b in (0,1):
   c=step(a,b)
   if c not in ids:
    if len(ids)>=limit:return None
    ids[c]=len(ids);todo.append(c)
   out.append(ids[c])
  D.append(tuple(out))
 return D

def prefix(base,k,limit=50000):
 def step(a,b):
  q,w=a
  w=w+str(b)
  if len(w)>k:q=base[q][int(w[0])];w=w[1:]
  return q,w
 return build((0,''),step,limit)

def maskDfa(mask):
 m=len(mask);all=(1<<m)-1;ones=sum(1<<i for i,b in enumerate(mask) if b=='?')
 def push(v,b):
  v=(v>>1)|((v&1)<<(m-1));return v&ones if b else v
 return build(all,push)

def leftDfa(mod):
 def push(s,b):
  kind,n=s
  if kind==4:return s
  if kind==0:return (2,1%mod) if b else (1,1%mod)
  if kind==1:return (3,1%mod) if b else (1,(n+1)%mod)
  if b:return kind,(n+1)%mod
  return 4,0
 return build((0,0),push)

if __name__=='__main__':
 s='1RB0LA_1RC0RE_0RD1RE_0LD1LB_1LA1RF_0RB---'
 mask=''.join('?' if i in {2,4} else '0' for i in range(5));R=maskDfa(mask)
 print('base R',len(R),flush=True)
 for mod in (5,10,1):
  L=leftDfa(mod)
  for k,l in [(4,4),(5,5),(6,6),(7,6),(6,7),(8,6),(6,8),(8,8)]:
   a=prefix(L,k);b=prefix(R,l)
   if a is None or b is None:continue
   start=time.monotonic();I=inv(s,a,b);print(mod,k,l,len(a),len(b),None if I is None else len(I),time.monotonic()-start,flush=True)
   if I:print(json.dumps(['10',s,a,b,I,[mod,k,l]]));sys.exit(0)
