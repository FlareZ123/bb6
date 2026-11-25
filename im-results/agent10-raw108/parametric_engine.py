from dataclasses import dataclass

# A part is (word,kind): literal, shared repetition n, or arbitrary untouched tail.
def clean(parts):
 out=[]
 for w,b in parts:
  if not w:continue
  if b==0 and out and out[-1][1]==0:out[-1]=(out[-1][0]+w,0)
  else:out.append((w,b))
 return tuple(out)
def lit(w):return ((w,0),) if w else ()
def rep(w):return ((w,1),)
def opaque(w):return ((w,2),)
def prefix(w):return w[0][0] if w and w[0][1]==0 else ''
def rest(w):return w[1:] if prefix(w) else w
def head(w):
 if not w:return '0'
 if w[0][1]:raise ValueError('opaque head')
 return w[0][0][0]
def tail(w):
 if not w:return ()
 if w[0][1]:raise ValueError('opaque tail')
 return clean(lit(w[0][0][1:])+w[1:])
def cons(a,w):return clean(lit(a)+w)
def normalization(w):
 hist=[];w=clean(w)
 while True:
  for i in range(1,len(w)):
   p,pr=w[i-1];b,br=w[i]
   if pr==0 and br==1 and p[-1]==b[-1]:
    ch=p[-1];pre=clean(w[:i-1]+lit(p[:-1]));suf=w[i+1:]
    v=clean(pre+rep(ch+b[:-1])+lit(ch)+suf)
    hist.append((w,v,pre,suf,b[:-1],ch));w=v;break
  else:return w,hist
@dataclass(frozen=True)
class C:
 q:int;l:tuple;r:tuple
 def norm(self):return self.q,normalization(self.l)[0],normalization(self.r)[0]
def step(c):
 a=p[2*c.q+int(head(c.l))]
 if a=='---':raise ValueError('hole')
 q,w=ord(a[2])-65,a[0]
 if a[1]=='R':return C(q,cons(head(c.r),cons(w,tail(c.l))),tail(c.r))
 return C(q,tail(c.l),cons(w,c.r))
def local(q,lp,rp,side,I,limit=150):
 c=C(q,lit(lp+(I if side=='L' else ''))+opaque('X'),lit(rp+(I if side=='R' else ''))+opaque('Y'))
 for k in range(1,limit+1):
  try:c=step(c)
  except ValueError:return None
  if c.q!=q:continue
  l,r=prefix(c.l),prefix(c.r)
  if rest(c.l)!=opaque('X') or rest(c.r)!=opaque('Y'):continue
  if side=='L' and l==lp and r.startswith(rp) and len(r)==len(rp)+len(I):return k,r[len(rp):]
  if side=='R' and r==rp and l.startswith(lp) and len(l)==len(lp)+len(I):return k,l[len(lp):]
 return None
def pump(start,target,limit=3000):
 c=start;hist=[];seen=set()
 for i in range(limit):
  if c.norm()==target.norm():return hist,c
  if c in seen:return None,c
  seen.add(c);ok=False
  for sd in ['L','R']:
   w,o=(c.l,c.r) if sd=='L' else (c.r,c.l)
   lp=prefix(w);wr=rest(w);op=prefix(o)
   if not wr or wr[0][1]!=1:continue
   I=wr[0][0]
   for j in range(min(32,len(op))+1):
    ans=local(c.q,lp if sd=='L' else op[:j],op[:j] if sd=='L' else lp,sd,I)
    if not ans:continue
    k,O=ans;w2=clean(lit(lp)+wr[1:]);o2=clean(lit(op[:j])+rep(O)+lit(op[j:])+rest(o))
    d=C(c.q,w2,o2) if sd=='L' else C(c.q,o2,w2)
    hist.append(('loop',c,d,k,sd,I,O,j));c=d;ok=True;break
   if ok:break
  if ok:continue
  try:d=step(c)
  except ValueError:return None,c
  hist.append(('step',c,d,1));c=d
 return None,c
