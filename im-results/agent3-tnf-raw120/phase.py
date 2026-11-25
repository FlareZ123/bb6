"""Independent-exponent extension of Agent10/31 symbolic sweep search.
All emitted equalities are kernel checked; discovery itself is untrusted."""
from dataclasses import dataclass
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/"agent31-three-hole-tnf"))
from generate_sweeps import parse

def clean(parts):
 out=[]
 for w,b in parts:
  if not w:continue
  if not b and out and not out[-1][1]:out[-1]=(out[-1][0]+w,False)
  else:out.append((w,b))
 return tuple(out)
def lit(w):return ((w,False),) if w else ()
def rep(w,v="n"):return ((w,v),)
def prefix(w):return w[0][0] if w and not w[0][1] else ''
def rest(w):return w[1:] if prefix(w) else w
def head(w):
 if not w:return '0'
 if w[0][1]:raise ValueError('opaque')
 return w[0][0][0]
def tail(w):
 if not w:return ()
 if w[0][1]:raise ValueError('opaque')
 return clean(lit(w[0][0][1:])+w[1:])
def cons(a,w):return clean(lit(a)+w)
def normalization(w):
 hist=[];w=clean(w)
 while True:
  for i in range(1,len(w)):
   p,pr=w[i-1];b,br=w[i]
   if not pr and br and p[-1]==b[-1]:
    ch=p[-1];pre=clean(w[:i-1]+lit(p[:-1]));suf=w[i+1:];v=clean(pre+rep(ch+b[:-1],br)+lit(ch)+suf);hist.append((w,v,pre,suf,b[:-1],ch));w=v;break
  else:return w,hist
@dataclass(frozen=True)
class C:
 q:int;l:tuple;r:tuple
 def norm(self):return self.q,normalization(self.l)[0],normalization(self.r)[0]
def step(p,c):
 a=p[2*c.q+int(head(c.l))]
 if a=='---':raise ValueError('hole')
 q,w=ord(a[2])-65,a[0]
 if a[1]=='R':return C(q,cons(head(c.r),cons(w,tail(c.l))),tail(c.r))
 return C(q,tail(c.l),cons(w,c.r))
def local(p,q,lp,rp,side,I,limit=100):
 c=C(q,lit(lp+(I if side=='L' else ''))+rep('X'),lit(rp+(I if side=='R' else ''))+rep('Y'))
 for k in range(1,limit+1):
  try:c=step(p,c)
  except ValueError:return None
  if c.q!=q:continue
  l,r=prefix(c.l),prefix(c.r)
  if rest(c.l)!=rep('X') or rest(c.r)!=rep('Y'):continue
  if side=='L' and l==lp and r.startswith(rp) and len(r)==len(rp)+len(I):return k,r[len(rp):]
  if side=='R' and r==rp and l.startswith(lp) and len(l)==len(lp)+len(I):return k,l[len(lp):]
 return None
def pump(p,start,target,limit=500):
 c=start;hist=[];seen=set()
 for _ in range(limit):
  if c.norm()==target.norm():return hist,c
  if c in seen:return None
  seen.add(c);ok=False
  for sd in ['L','R']:
   w,o=(c.l,c.r) if sd=='L' else (c.r,c.l);lp=prefix(w);wr=rest(w);op=prefix(o)
   if not wr:continue
   I,var=wr[0]
   for j in range(min(16,len(op))+1):
    ans=local(p,c.q,lp if sd=='L' else op[:j],op[:j] if sd=='L' else lp,sd,I)
    if not ans:continue
    k,O=ans;w2=clean(lit(lp)+wr[1:]);o2=clean(lit(op[:j])+rep(O,var)+lit(op[j:])+rest(o));d=C(c.q,w2,o2) if sd=='L' else C(c.q,o2,w2);hist.append(('loop',c,d,k,sd,I,O,j,var));c=d;ok=True;break
   if ok:break
  if ok:continue
  try:d=step(p,c)
  except ValueError:return None
  hist.append(('step',c,d,1));c=d
 return None
def bits(s): return '['+','.join('true' if b=='1' else 'false' for b in s)+']'
def app(*xs): return ' ++ '.join('('+x+')' for x in xs if x!='[]') or '[]'
def word(w): return app(*[f'rep {bits(s)} ({v})' if v else bits(s) for s,v in w])
def cfg(c): return f'⟨{c.q},{word(c.l)},{word(c.r)}⟩'
def cf(q,l,r): return f'⟨{q},{l},{r}⟩'
def tab(p):
 out=['def table : PartialMachine := fun s =>','  match s.1.val,s.2 with']
 for i,a in enumerate(p):
  if a!='---':out.append(f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(a[0]=="1").lower()},{str(a[1]=="R").lower()},{ord(a[2])-65}⟩)')
 out.append('  | _,_ => none');return '\n'.join(out)
SIMP='List.append_assoc,List.cons_append,List.nil_append,List.append_nil'
def wordeq(name,a,b,variables):
 lhs=word(a) if a else '([] : List Bool)';binders=' '.join(variables)
 ls=[f'theorem {name} ({binders} : Nat) : {lhs} = {word(b)} := by'] if variables else [f'theorem {name} : {lhs} = {word(b)} := by']
 if a==b:return '\n'.join(ls+['  rfl'])
 x,xs=normalization(a);y,ys=normalization(b);assert x==y
 while xs and ys and xs[-1]==ys[-1]:xs.pop();ys.pop()
 ls.append('  calc')
 for u,v,pre,suf,k,z in xs:
  var=next(tag for w,tag in v[len(pre):] if tag)
  ls.append(f'    _ = {word(v)} := by simpa only [{SIMP}] using moveCut ({word(pre)}) ({word(suf)}) {bits(k)} {str(z=="1").lower()} {var}')
 for u,v,pre,suf,k,z in reversed(ys):
  var=next(tag for w,tag in v[len(pre):] if tag)
  ls.append(f'    _ = {word(u)} := by symm; simpa only [{SIMP}] using moveCut ({word(pre)}) ({word(suf)}) {bits(k)} {str(z=="1").lower()} {var}')
 return '\n'.join(ls)
def generate_phase(name,p,start,target,ans,variables=('n',)):
 hist,last=ans;ls=[f'namespace {name}'];seg=[];i=0
 while i<len(hist):
  x=hist[i]
  if x[0]=='step':
   j=i+1
   while j<len(hist) and hist[j][0]=='step':j+=1
   seg.append(('fixed',x[1],hist[j-1][2],j-i));i=j
  else:seg.append(x);i+=1
 binders=' '.join(variables);vb=f' ({binders} : Nat)' if binders else '';args=' '.join(variables);argsp=' '+args if args else ''
 costs=[]
 for j,x in enumerate(seg):
  typ,c,d,k=x[:4]
  if typ=='fixed':
   ls.append(f'theorem phase{j}{vb} : run0 table {k} {cfg(c)} = some {cfg(d)} := by rfl');costs.append(str(k));continue
  _,_,_,k,side,I,O,cut,var=x
  if side=='L':
   lp,rp=prefix(c.l),prefix(c.r)[:cut];L,R=rest(c.l)[1:],clean(lit(prefix(c.r)[cut:])+rest(c.r));src=cf(c.q,app(bits(lp),bits(I),'L'),app(bits(rp),'R'));dst=cf(c.q,app(bits(lp),'L'),app(bits(rp),bits(O),'R'))
  else:
   lp,rp=prefix(c.l)[:cut],prefix(c.r);L,R=clean(lit(prefix(c.l)[cut:])+rest(c.l)),rest(c.r)[1:];src=cf(c.q,app(bits(lp),'L'),app(bits(rp),bits(I),'R'));dst=cf(c.q,app(bits(lp),bits(O),'L'),app(bits(rp),'R'))
  ls.append(f'theorem local{j} (L R : List Bool) : run0 table {k} {src} = some {dst} := by rfl')
  ls.append(f'theorem phase{j}{vb} : run0 table ({k}*{var}) {cfg(c)} = some {cfg(d)} := by\n  simpa only [{SIMP}] using sweep{side} table {c.q} {bits(lp)} {bits(rp)} {bits(I)} {bits(O)} {k} local{j} {var} ({word(L)}) ({word(R)})');costs.append(f'{k}*{var}')
 for sd,w,v in [('L',last.l,target.l),('R',last.r,target.r)]:
  if w!=v:ls.append(wordeq('final'+sd,w,v,variables))
 a=sum(x[3] for x in seg if x[0]=='fixed');bs={var:sum(x[3] for x in seg if x[0]=='loop' and x[-1]==var) for var in variables};cost='+'.join([str(a)]+[f'{b}*{var}' for var,b in bs.items() if b]);assert a>0
 proof=f'theorem advance{vb} : run0 table ({cost}) {cfg(start)} = some {cfg(target)} := by\n'
 join=f'(phase0{argsp})'
 for j in range(1,len(seg)):join=f'(join0 {join} (phase{j}{argsp}))'
 proof+=f'  have H := {join}\n'
 for sd,w,v in [('L',last.l,target.l),('R',last.r,target.r)]:
  if w!=v:proof+=f'  rw [final{sd}{argsp}] at H\n'
 proof+=f'  rw [show {"+".join(costs)}={cost} by omega] at H\n  exact H';ls.extend([proof,f'end {name}']);return '\n\n'.join(ls),cost

def c_right(q,*parts):return C(q,(),clean(tuple(parts)))
def c_left(q,*parts):return C(q,clean(tuple(parts)),())
