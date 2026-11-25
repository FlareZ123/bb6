"""Two independent exponent symbolic transfer search, generating exact Lean phases."""
from dataclasses import dataclass
import multi as m
import generate_sweeps as g
from functools import lru_cache

def lit(w): return ((w,''),) if w else ()
def rep(w,v): return ((w,v),)
def clean(parts):
 out=[]
 for w,v in parts:
  if not w:continue
  if not v and out and not out[-1][1]:out[-1]=(out[-1][0]+w,'')
  else:out.append((w,v))
 return tuple(out)
def pre(w):return w[0][0] if w and not w[0][1] else ''
def rest(w):return w[1:] if pre(w) else w
def hd(w):
 if not w:return '0'
 if w[0][1]:raise ValueError('opaque head')
 return w[0][0][0]
def tl(w):
 if not w:return ()
 if w[0][1]:raise ValueError('opaque tail')
 return clean(lit(w[0][0][1:])+w[1:])
def cons(b,w):return clean(lit(b)+w)
def norm(w):
 out=[]
 def add(b,a):
  if out and out[-1][0]==b:out[-1]=(b,tuple(x+y for x,y in zip(out[-1][1],a)))
  else:out.append((b,a))
 for s,v in w:
  if v:
   assert len(set(s))==1,(s,v)
   add(s[0],(0,len(s) if v=='n' else 0,len(s) if v=='j' else 0))
  else:
   for b in s:add(b,(1,0,0))
 return tuple(out)
@dataclass(frozen=True)
class C:
 q:int;l:tuple;r:tuple
 def norm(self):return self.q,norm(self.l),norm(self.r)
def step(p,c):
 a=p[2*c.q+int(hd(c.l))]
 if a=='---':raise ValueError('hole')
 q,w=ord(a[2])-65,a[0]
 if a[1]=='R':return C(q,cons(hd(c.r),cons(w,tl(c.l))),tl(c.r))
 return C(q,tl(c.l),cons(w,c.r))
local=lru_cache(None)(m.local)
def pump(p,start,target,limit=40):
 from collections import deque
 todo=deque([(start,[])]);seen={start}
 while todo and len(seen)<10000:
  c,h=todo.popleft()
  if c.norm()==target.norm():return h,c
  if len(h)>limit:continue
  nxt=[]
  for sd in ('L','R'):
   w,o=(c.l,c.r) if sd=='L' else (c.r,c.l);lp=pre(w);wr=rest(w);op=pre(o)
   if not wr:continue
   I,v=wr[0];assert v
   for cut in range(min(16,len(op))+1):
    ans=local(p,c.q,lp if sd=='L' else op[:cut],op[:cut] if sd=='L' else lp,sd,I)
    if not ans:continue
    k,O=ans
    if len(set(O))!=1:continue
    w2=clean(lit(lp)+wr[1:]);o2=clean(lit(op[:cut])+rep(O,v)+lit(op[cut:])+rest(o))
    d=C(c.q,w2,o2) if sd=='L' else C(c.q,o2,w2)
    nxt.append((d,('loop',c,d,k,sd,I,O,cut,v)))
  try:
   d=step(p,c);nxt.append((d,('step',c,d,1)))
  except ValueError:pass
  for d,a in nxt:
   if d not in seen:seen.add(d);todo.append((d,h+[a]))
 return None
def E(l,r=()):return C(4,clean(l),clean(r))
def family():return E(lit('01111')+rep('11','n'))
def mid(nextra=0,jextra=0,variable=True):
 return E(lit('0'+'1'*(2+2*nextra))+(rep('11','n') if variable else ())+lit('0'+'1'*(1+jextra))+rep('1','j'),lit('1'*(1+jextra))+rep('1','j'))
def phases(p):
 first=E(lit('01111')+rep('11','n')); next_=E(lit('011')+rep('11','n')+lit('01'),lit('1'))
 inner=mid(1); target=mid(0,1)
 end=mid(0,0,False); finish=E(lit('0111111')+rep('11','j'))
 return [(name,st,tg,pump(p,st,tg)) for name,st,tg in [('first',first,next_),('inner',inner,target),('finish',end,finish)]]
