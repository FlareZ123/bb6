"""Counter descents using arbitrary right tails and a nonnegative exponent."""
import quad as q
import quad_codegen as gen
import generate_sweeps as g
from collections import deque

# Replace only normalization/pumping support: R is an arbitrary list never read in descent.
def norm(w):
 out=[]
 def add(b,a):
  if out and out[-1][0]==b and b!='X':out[-1]=(b,tuple(x+y for x,y in zip(out[-1][1],a)))
  else:out.append((b,a))
 for s,v in w:
  if v=='R':add('X',(1,0,0))
  elif v:
   assert len(set(s))==1,(s,v)
   add(s[0],(0,len(s),0))
  else:
   for b in s:add(b,(1,0,0))
 return tuple(out)
q.norm=norm

def pump(p,start,target,limit=40):
 todo=deque([(start,[])]);seen={start}
 while todo and len(seen)<10000:
  c,h=todo.popleft()
  if c.norm()==target.norm():return h,c
  if len(h)>limit:continue
  nxt=[]
  for sd in ('L','R'):
   w,o=(c.l,c.r) if sd=='L' else (c.r,c.l);lp=q.pre(w);wr=q.rest(w);op=q.pre(o)
   if not wr:continue
   I,v=wr[0];assert v
   if v=='R':continue
   for cut in range(min(16,len(op))+1):
    ans=q.local(p,c.q,lp if sd=='L' else op[:cut],op[:cut] if sd=='L' else lp,sd,I)
    if not ans:continue
    k,O=ans
    if len(set(O))!=1:continue
    w2=q.clean(q.lit(lp)+wr[1:]);o2=q.clean(q.lit(op[:cut])+q.rep(O,v)+q.lit(op[cut:])+q.rest(o))
    d=q.C(c.q,w2,o2) if sd=='L' else q.C(c.q,o2,w2)
    nxt.append((d,('loop',c,d,k,sd,I,O,cut,v)))
  try:
   d=q.step(p,c);nxt.append((d,('step',c,d,1)))
  except ValueError:pass
  for d,a in nxt:
   if d not in seen:seen.add(d);todo.append((d,h+[a]))
 return None

def desc(p,k,suf):
 target=q.E(q.lit('0'+'1'*k+suf),q.rep('0','n')+q.lit('1')+q.rep('X','R'))
 for a in range(k+2):
  st=q.E(q.lit('0'+'1'*a)+q.rep('1','n')+q.lit('1'*(k+1-a)+suf),q.rep('X','R'))
  ans=pump(p,st,target)
  if ans:return st,target,ans
 return None

SPECS={4463:(5,'0',23,25,3,32,1),4759:(4,'0',27,31,5,35,1),8393:(5,'01110',25,27,3,41,0),9402:(5,'01110',25,27,3,41,0),10521:(4,'00',19,19,1,27,1)}
