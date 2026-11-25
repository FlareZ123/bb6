"""Independent-counter symbolic sweeps; every emitted equation is Lean-checked."""
from dataclasses import dataclass
import multi as m

def lit(w):return ((w,''),) if w else ()
def rep(w,n):return ((w,n),)
def clean(parts):
 out=[]
 for w,v in parts:
  if not w:continue
  if not v and out and not out[-1][1]:out[-1]=(out[-1][0]+w,'')
  else:out.append((w,v))
 return tuple(out)
def prefix(w):return w[0][0] if w and not w[0][1] else ''
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
@dataclass(frozen=True)
class C:
 q:int;l:tuple;r:tuple
 def __str__(self):return f'{chr(65+self.q)} '+fmt(self.l)+' | '+fmt(self.r)
def fmt(w):return ''.join(s if not v else f'({s})^{v}' for s,v in w) or '[]'
def step(p,c):
 a=p[2*c.q+int(head(c.l))]
 if a=='---':raise ValueError('hole')
 q,w=ord(a[2])-65,a[0]
 if a[1]=='R':return C(q,cons(head(c.r),cons(w,tail(c.l))),tail(c.r))
 return C(q,tail(c.l),cons(w,c.r))
def walk(p,start,stop,limit=4000):
 c=start;hist=[];seen=set()
 for _ in range(limit):
  if hist and stop(c):return hist,c
  if c in seen:raise ValueError('cycle '+str(c))
  seen.add(c);ok=False
  for sd in ['L','R']:
   w,o=(c.l,c.r) if sd=='L' else (c.r,c.l);lp=prefix(w);wr=rest(w);op=prefix(o)
   if not wr:continue
   I,v=wr[0]
   if I in ('X','Y'):continue
   for j in range(min(16,len(op))+1):
    ans=m.local(p,c.q,lp if sd=='L' else op[:j],op[:j] if sd=='L' else lp,sd,I)
    if not ans:continue
    k,O=ans;w2=clean(lit(lp)+wr[1:]);o2=clean(lit(op[:j])+rep(O,v)+lit(op[j:])+rest(o));d=C(c.q,w2,o2) if sd=='L' else C(c.q,o2,w2);hist.append(('loop',c,d,k,sd,I,O,j,v));c=d;ok=True;break
   if ok:break
  if ok:continue
  try:d=step(p,c)
  except ValueError as e:raise ValueError(f'{e}: {c}, after {len(hist)} actions')
  hist.append(('step',c,d,1));c=d
 raise ValueError(f'limit {c}')
def bits(s):return '['+','.join('true' if a=='1' else 'false' for a in s)+']'
def app(*xs):return '('+'++'.join(x for x in xs if x!='[]')+')' if any(x!='[]' for x in xs) else '[]'
def word(w):return app(*[('R' if s=='X' else 'L' if s=='Y' else f'rep {bits(s)} {v}') if v else bits(s) for s,v in w])
def cfg(c):return f'⟨{c.q},{word(c.l)},{word(c.r)}⟩'
def cf(q,l,r):return f'⟨{q},{l},{r}⟩'
def tab(p):
 lines=['def table : PartialMachine := fun s => match s.1.val,s.2 with']
 for i,a in enumerate(p):
  if a=='---':continue
  lines.append(f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(a[0]=="1").lower()},{str(a[1]=="R").lower()},{ord(a[2])-65}⟩)')
 return '\n'.join(lines+['  | _,_ => none'])
SIMP='List.append_assoc,List.cons_append,List.nil_append,List.append_nil'
def generate(p,name,st,result):
 hist,tg=result;seg=[];i=0
 while i<len(hist):
  x=hist[i]
  if x[0]=='step':
   j=i+1
   while j<len(hist) and hist[j][0]=='step':j+=1
   seg.append(('fixed',x[1],hist[j-1][2],j-i));i=j
  else:seg.append(x);i+=1
 vs=sorted({v for s,v in st.l+st.r if v and s not in ('X','Y')});rs=sorted({s for s,v in st.l+st.r if s in ('X','Y')});tails=['R' if s=='X' else 'L' for s in rs];binders=(' ('+' '.join(vs)+' : Nat)' if vs else '')+(' ('+' '.join(tails)+' : List Bool)' if tails else '');args=' '.join(vs+tails)
 ls=[f'namespace {name}'];costs=[]
 for j,x in enumerate(seg):
  typ,c,d,k=x[:4]
  if typ=='fixed':
   ls.append(f'theorem phase{j}{binders} : run0 table {k} {cfg(c)} = some {cfg(d)} := by rfl');costs.append(str(k));continue
  _,_,_,k,side,I,O,cut,v=x
  if side=='L':
   lp,rp=prefix(c.l),prefix(c.r)[:cut];L,R=rest(c.l)[1:],clean(lit(prefix(c.r)[cut:])+rest(c.r));src=cf(c.q,app(bits(lp),bits(I),'L'),app(bits(rp),'R'));dst=cf(c.q,app(bits(lp),'L'),app(bits(rp),bits(O),'R'))
  else:
   lp,rp=prefix(c.l)[:cut],prefix(c.r);L,R=clean(lit(prefix(c.l)[cut:])+rest(c.l)),rest(c.r)[1:];src=cf(c.q,app(bits(lp),'L'),app(bits(rp),bits(I),'R'));dst=cf(c.q,app(bits(lp),bits(O),'L'),app(bits(rp),'R'))
  ls.append(f'theorem local{j} (L R : List Bool) : run0 table {k} {src} = some {dst} := by rfl')
  ls.append(f'theorem phase{j}{binders} : run0 table ({k}*{v}) {cfg(c)} = some {cfg(d)} := by\n  simpa only [{SIMP}] using sweep{side} table {c.q} {bits(lp)} {bits(rp)} {bits(I)} {bits(O)} {k} local{j} {v} {word(L)} {word(R)}')
  costs.append(f'{k}*{v}')
 a=sum(x[3] for x in seg if x[0]=='fixed'); coeff={v:sum(x[3] for x in seg if x[0]=='loop' and x[-1]==v) for v in vs};cost='+'.join([str(a)]+[f'{k}*{v}' for v,k in coeff.items() if k]);join=f'(phase0 {args})'
 for j in range(1,len(seg)):join=f'(join0 {join} (phase{j} {args}))'
 eq=f'theorem equation{binders} : run0 table ({cost}) {cfg(st)} = some {cfg(tg)} := by\n  have H := {join}\n'
 if "+".join(costs)!=cost:eq+=f'  rw [show {"+".join(costs)}={cost} by omega] at H\n'
 ls.append(eq+"  exact H");ls.append(f'end {name}')
 return '\n\n'.join(ls),cost
