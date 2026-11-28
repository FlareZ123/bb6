"""One-parameter symbolic tape sweeps. Candidate discovery; Lean validates all steps."""
from collections import defaultdict
from functools import lru_cache
from dataclasses import dataclass
from itertools import product
import sys,hashlib
from pathlib import Path

def clean(xs):
 out=[]
 for w,b in xs:
  if not w:continue
  if not b and out and not out[-1][1]:out[-1]=(out[-1][0]+w,False)
  else:out.append((w,b))
 return tuple(out)
def lit(w):return ((w,False),) if w else ()
def rep(w):return ((w,True),) if w else ()
def prefix(w):return w[0][0] if w and not w[0][1] else ''
def rest(w):return w[1:] if prefix(w) else w
def pop(w):
 if not w:return '0',()
 if w[0][1]:raise ValueError('opaque')
 return w[0][0][0],clean(lit(w[0][0][1:])+w[1:])
def cons(w,a):return clean(lit(w)+a)
def normalize(w):
 hist=[];w=clean(w)
 while True:
  for i in range(1,len(w)):
   p,pr=w[i-1];b,br=w[i]
   if not pr and br and p[-1]==b[-1]:
    z=p[-1];pre=clean(w[:i-1]+lit(p[:-1]));suf=w[i+1:];v=clean(pre+rep(z+b[:-1])+lit(z)+suf)
    hist.append((w,v,pre,suf,b[:-1],z));w=v;break
  else:return w,hist
@dataclass(frozen=True)
class C:
 q:int;l:tuple;r:tuple
 def norm(self):return self.q,normalize(self.l)[0],normalize(self.r)[0]

def step(row,c):
 b,l=pop(c.l);a=row[2*c.q+int(b)]
 if a<=0:raise ValueError('terminal')
 a-=1;q=a>>2;w=str((a>>1)&1)
 if a&1:
  b,r=pop(c.r);return C(q,cons(b+w,l),r)
 return C(q,l,cons(w,c.r))

def trace(row,N=2500):
 c=C(0,(),());out=[c]
 for i in range(N):
  try:c=step(row,c)
  except ValueError:break
  out.append(c)
 return out

def evaluate(w,n):return ''.join(s*n if b else s for s,b in w)
def nextword(w):return clean(tuple(x for a,b in w for x in ((a,False),(a,True)) if b) if all(b for _,b in w) else tuple(x for a,b in w for x in (((a,False),(a,True)) if b else ((a,False),))))

@lru_cache(maxsize=50000)
def local(row,q,lp,rp,side,I,limit=100):
 c=C(q,lit(lp+(I if side=='L' else ''))+rep('X'),lit(rp+(I if side=='R' else ''))+rep('Y'))
 for k in range(1,limit+1):
  try:c=step(row,c)
  except ValueError:return None
  if c.q!=q:continue
  l,r=prefix(c.l),prefix(c.r)
  if rest(c.l)!=rep('X') or rest(c.r)!=rep('Y'):continue
  if side=='L' and l==lp and r.startswith(rp):return k,r[len(rp):]
  if side=='R' and r==rp and l.startswith(lp):return k,l[len(lp):]
 return None

def loops(row,c):
 for side,w,o in [('L',c.l,c.r),('R',c.r,c.l)]:
  lp=prefix(w);wr=rest(w);op=prefix(o)
  if not wr or not wr[0][1]:continue
  I=wr[0][0]
  for cut in range(min(24,len(op))+1):
   a=local(row,c.q,lp if side=='L' else op[:cut],op[:cut] if side=='L' else lp,side,I)
   if a is None:continue
   k,O=a;w2=clean(lit(lp)+wr[1:]);o2=clean(lit(op[:cut])+rep(O)+lit(op[cut:])+rest(o))
   d=C(c.q,w2,o2) if side=='L' else C(c.q,o2,w2)
   yield ('loop',c,d,k,side,I,O,cut)

def solve(row,start,target,limit=150):
 goal=target.norm();stack=[(start,[])];seen=set()
 while stack:
  c,ops=stack.pop()
  if ops and c.norm()==goal:return ops,c
  if len(ops)>=limit or c in seen:continue
  if sum(len(x) for w in (c.l,c.r) for x,_ in w)>250:continue
  seen.add(c)
  if len(seen)>5000:return None
  try:d=step(row,c);stack.append((d,ops+[('step',c,d,1)]))
  except ValueError:pass
  for op in loops(row,c):stack.append((op[2],ops+[op]))
 return None

def insertions(a,b):
 d=len(b)-len(a)
 if d<0 or d>32:return []
 if d==0:return [()] if a==b else []
 return [(i,b[i:i+d]) for i in range(len(a)+1) if a[:i]==b[:i] and a[i:]==b[i+d:]]
def form(a,ins):
 if not ins:return lit(a)
 i,w=ins;return clean(lit(a[:i])+rep(w)+lit(a[i:]))

def candidates(tr):
 cs=[(c.q,evaluate(c.l,0),evaluate(c.r,0)) for c in tr];inds=defaultdict(list)
 for i,c in enumerate(cs):inds[c].append(i)
 for i,(q,l,r) in sorted(enumerate(cs[:500]),key=lambda x:(min(map(len,x[1][1:])),sum(map(len,x[1][1:])),x[0])):
  for j in range(i+1,min(len(cs),i+650)):
   s,m,n=cs[j]
   if s!=q or len(m)+len(n)<=len(l)+len(r):continue
   for il,ir in product(insertions(l,m),insertions(r,n)):
    a=C(q,form(l,il),form(r,ir));e=q,evaluate(a.l,2),evaluate(a.r,2)
    if any(k>j for k in inds.get(e,())):yield i,a

def find(row,N=2500):
 row=tuple(row);tr=trace(row,N);seen=set()
 for i,a in candidates(tr):
  key=a.norm()
  if key in seen:continue
  seen.add(key)
  if len(seen)>200:break
  target=C(a.q,nextword(a.l),nextword(a.r));ans=solve(row,a,target)
  if ans:return i,a,target,ans
 return None

SIMP='List.append_assoc,List.cons_append,List.nil_append,List.append_nil'
def bits(w):return '['+','.join('true' if b=='1' else 'false' for b in w)+']'
def app(*xs):return ' ++ '.join('('+x+')' for x in xs if x!='[]') or '[]'
def word(w):return app(*[f'rep {bits(s)} n' if b else bits(s) for s,b in w])
def cfg(c):return f'⟨{c.q},{word(c.l)},{word(c.r)}⟩'
def cf(q,l,r):return f'⟨{q},{l},{r}⟩'
def wordeq(name,a,b):
 lhs=word(a) if a else '([] : List Bool)';ls=[f'theorem {name} (n : Nat) : {lhs} = {word(b)} := by']
 if a==b:return '\n'.join(ls+['  rfl'])
 x,xs=normalize(a);y,ys=normalize(b);assert x==y
 while xs and ys and xs[-1]==ys[-1]:xs.pop();ys.pop()
 ls.append('  calc')
 for _,v,pre,suf,k,z in xs:ls.append(f'    _ = {word(v)} := by simpa only [{SIMP}] using moveCut ({word(pre)}) ({word(suf)}) {bits(k)} {str(z=="1").lower()} n')
 for v,_,pre,suf,k,z in reversed(ys):ls.append(f'    _ = {word(v)} := by symm; simpa only [{SIMP}] using moveCut ({word(pre)}) ({word(suf)}) {bits(k)} {str(z=="1").lower()} n')
 return '\n'.join(ls)
def generate(idx,row,ans):
 t,st,target,(hist,last)=ans
 ls=[f'namespace M{idx}',f'-- {list(row)}','def table : PartialMachine := fun s =>','  match s.1.val,s.2 with']
 for i,v in enumerate(row):
  if v>0:
   a=v-1;ls.append(f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(bool((a>>1)&1)).lower()},{str(bool(a&1)).lower()},{a>>2}⟩)')
  elif v==0:ls.append(f'  | {i//2},{str(bool(i%2)).lower()} => some none')
 ls+=['  | _,_ => none',f'def family (n : Nat) : Z0 := {cfg(st)}',f'theorem entry : run0 table {t} ⟨0,[],[]⟩ = some (family 0) := by rfl']
 seg=[];i=0
 while i<len(hist):
  x=hist[i]
  if x[0]=='step':
   j=i+1
   while j<len(hist) and hist[j][0]=='step':j+=1
   seg.append(('fixed',x[1],hist[j-1][2],j-i));i=j
  else:seg.append(x);i+=1
 costs=[]
 for j,x in enumerate(seg):
  typ,c,d,k=x[:4]
  if typ=='fixed':ls.append(f'theorem phase{j} (n : Nat) : run0 table {k} {cfg(c)} = some {cfg(d)} := by rfl');costs.append(str(k));continue
  _,_,_,k,side,I,O,cut=x
  if side=='L':
   lp,rp=prefix(c.l),prefix(c.r)[:cut];L,R=rest(c.l)[1:],clean(lit(prefix(c.r)[cut:])+rest(c.r));src=cf(c.q,app(bits(lp),bits(I),'L'),app(bits(rp),'R'));dst=cf(c.q,app(bits(lp),'L'),app(bits(rp),bits(O),'R'))
  else:
   lp,rp=prefix(c.l)[:cut],prefix(c.r);L,R=clean(lit(prefix(c.l)[cut:])+rest(c.l)),rest(c.r)[1:];src=cf(c.q,app(bits(lp),'L'),app(bits(rp),bits(I),'R'));dst=cf(c.q,app(bits(lp),bits(O),'L'),app(bits(rp),'R'))
  ls.append(f'theorem local{j} (L R : List Bool) : run0 table {k} {src} = some {dst} := by rfl')
  ls.append(f'theorem phase{j} (n : Nat) : run0 table ({k}*n) {cfg(c)} = some {cfg(d)} := by\n  simpa only [{SIMP}] using sweep{side} table {c.q} {bits(lp)} {bits(rp)} {bits(I)} {bits(O)} {k} local{j} n ({word(L)}) ({word(R)})');costs.append(f'{k}*n')
 ls.extend((wordeq('finalL',last.l,target.l),wordeq('finalR',last.r,target.r)))
 a=sum(x[3] for x in seg if x[0]=='fixed');b=sum(x[3] for x in seg if x[0]=='loop')
 proof=f'theorem growth (n : Nat) : run0 table ({a}+{b}*n) (family n) = some (family (n+1)) := by\n';join='(phase0 n)'
 for j in range(1,len(seg)):join=f'(join0 {join} (phase{j} n))'
 proof+=f'  have H := {join}\n'
 for name,w,v in [('finalL',last.l,target.l),('finalR',last.r,target.r)]:
  if w!=v:proof+=f'  rw [{name} n] at H\n'
 proof+=f"  rw [show {'+'.join(costs)}={a}+{b}*n by omega] at H\n  simpa only [family,rep,{SIMP}] using H"
 ls.extend([proof,f'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=\n  never_of_growth table family {t} (fun n => {a}+{b}*n) entry (by intro n; omega) growth m hm','#print axioms never',f'end M{idx}'])
 return '\n'.join(ls),(t,a,b)

def job(item):
 i,row=item;ans=find(row)
 if ans is None:return i,row,None,None
 code,info=generate(i,row,ans);return i,row,code,info

if __name__=='__main__':
 from multiprocessing import Pool
 rowsfile,out=Path(sys.argv[1]),Path(sys.argv[2])
 out.mkdir(parents=True,exist_ok=True)
 alpha='0123456789abcdefghijklmnop'
 rows=[tuple(alpha.index(c)-1 for c in line) for line in rowsfile.read_text().splitlines()]
 assert len(rows)==412 and rows==sorted(set(rows))
 found=[]
 with Pool(int(sys.argv[3]) if len(sys.argv)>3 else 2) as p:
  for i,r,code,info in p.imap(job,enumerate(rows),chunksize=1):
   print(i,r,info,flush=True)
   if code:
    found.append(i)
    name=f'Box27Pump{i:04d}';path=out/(name+'.lean');path.write_text('import SweepPumping\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6Coverage.Agent31Pump\nopen BB6Coverage\n'+code+'\nend BB6Coverage.Agent31Pump\n')
 assert len(found)==294, len(found)
 digest=hashlib.sha256()
 for i in found:
  path=out/f'Box27Pump{i:04d}.lean'
  digest.update(path.name.encode()+b'\0'+path.read_bytes())
 assert digest.hexdigest()=='cec07de68df50bf110bf451221886fcb0d51986bb5cbc191c1201eb4012b9c13',digest.hexdigest()
 # All generated source files must subsequently be compiled with Lean.
 imports=''.join(f'import Box27Pump{i:04d}\n' for i in found)
 head='import Box27ProofBank\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent49.Box27PumpBank\nopen BB6Coverage BB6.Agent13BlankDelay BB6.Agent49.Box27Slice BB6.Agent49.Box27ProofBank\nopen BB6Coverage.Agent31Pump\n'
 items=',\n'.join(x for i in found for x in (f'  fromNever B M{i}.table M{i}.never',f'  conjugate B (fromNever B M{i}.table M{i}.never)'))
 tail='\ndef known (B : Nat) : Array PartialMachine := tables B (bank B)\ntheorem knownGood (B : Nat) : ∀ (i : Nat) (q : PartialMachine), (known B)[i]? = some q → Good B q := tables_good B (bank B)\n#print axioms knownGood\nend BB6.Agent49.Box27PumpBank\n'
 (out/'Box27PumpBank.lean').write_text(imports+head+'def bank (B : Nat) : Array (Certified B) := #[\n'+items+'\n]'+tail)
