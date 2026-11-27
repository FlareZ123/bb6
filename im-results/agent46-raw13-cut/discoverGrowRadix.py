"""Reproduce seven two-parameter growing-prefix radix-four certificates.
Run from the Raw13 cut directory; needs autoword.py and emitUnaryBank.py.
Generated instances are candidates until the individual Lean checks finish.
"""
from autoword import localstep,step
from dataclasses import dataclass
from pathlib import Path
import time,json,sys
@dataclass(frozen=True)
class W:
 pre:str
 block:str=''
 idx:int=0
 post:'W|str|None'=None
 def __post_init__(self):
  if self.block and not isinstance(self.post,W):object.__setattr__(self,'post',W(self.post or ''))
  if not self.block and self.post is not None:raise ValueError(self)
 def head(self):
  if self.pre:return self.pre[0]
  if not self.block:return '0'
  raise ValueError('unknown')
 def drop(self):
  if self.pre:return W(self.pre[1:],self.block,self.idx,self.post)
  if not self.block:return self
  raise ValueError('unknown')
 def prepend(self,x):return W(x+self.pre,self.block,self.idx,self.post)
 def norm(self):
  p,b,s=self.pre,self.block,self.post
  if not b:return self
  while p and p[-1]==b[-1]:
   c=p[-1];p=p[:-1];b=c+b[:-1];s=s.prepend(c)
  return W(p,b,self.idx,s.norm())
 def size(self):return len(self.pre)+(self.post.size() if self.block else 0)
 def pack(self):return [self.pre,self.block,self.idx,self.post.pack()] if self.block else self.pre
 def eval(self,n,m):return self.pre+self.block*(m if self.idx else n)+(self.post.eval(n,m) if self.block else '')
@dataclass(frozen=True)
class C:
 q:int
 l:W
 r:W
 def norm(self):return C(self.q,self.l.norm(),self.r.norm())
 def pack(self):return [self.q,self.l.pack(),self.r.pack()]
def symstep(t,z):
 q,l,r=z.q,z.l,z.r;w,d,p=t[3*(2*q+int(l.head())):][:3]
 if w=='-':raise ValueError('hole')
 q=ord(p)-65
 return C(q,l.drop().prepend(r.head()+w),r.drop()) if d=='R' else C(q,l.drop(),r.prepend(w))
def sweeps(t,z,maxsteps=400):
 for d in 'RL':
  a,b=(z.l,z.r) if d=='R' else (z.r,z.l)
  if not b.block:continue
  rp=b.pre;I=b.block;idx=b.idx
  for f in range(len(a.pre)+1):
   lp=a.pre[:f];L=W(a.pre[f:],a.block,a.idx,a.post);R=b.post
   s=(z.q,lp,rp+I) if d=='R' else (z.q,rp+I,lp)
   for k in range(1,maxsteps+1):
    s=localstep(t,s)
    if s is None:break
    q,x,y=s;x,y=(x,y) if d=='R' else (y,x)
    if q==z.q and y==rp and x.startswith(lp) and len(x)==len(lp)+len(I):
     O=x[len(lp):];aa=W(lp,O,idx,L);bb=R.prepend(rp)
     new=C(q,aa,bb) if d=='R' else C(q,bb,aa)
     if d=='L':lp,rp,L,R=rp,lp,R,L
     yield new,[d,lp,rp,I,O,L.pack(),R.pack(),idx,k]
     break
def prove(t,f,g,seconds=30,limit=1000,protected=False):
 deadline=time.monotonic()+seconds;target=g.norm();seen=set()
 def dfs(z,path,a,b,c):
  if z.norm()==target and path:return path,a,b,c
  if time.monotonic()>deadline or len(path)>=limit or z in seen:return None
  seen.add(z)
  for y,op in sweeps(t,z):
   if y==z:continue
   rr=dfs(y,path+[op],a+(op[-1] if op[-2]==0 else 0),b+(op[-1] if op[-2]==1 else 0),c)
   if rr:return rr
  try:
   if protected and not z.r.pre and not z.r.block and t[3*(2*z.q+int(z.l.head()))+1]=='R':return None
   y=symstep(t,z)
  except ValueError:return None
  if y.l.size()+y.r.size()>1000:return None
  return dfs(y,path+[None],a,b,c+1)
 res=dfs(f,[],0,0,0)
 if not res:return None
 path,a,b,c=res;ops=[]
 for op in path:
  if op is None:
   if ops and isinstance(ops[-1],int):ops[-1]+=1
   else:ops.append(1)
  else:ops.append(op)
 return dict(ops=ops,a=a,b=b,c=c)
TABLES={
20:"1RB1LD1RC0LD1LA1RE0LD0LA0RB0RF1LB---",
38:"1RB1LD1RC0LD1LA1RE0LF0LA0RB1RA---0LA",
39:"1RB1LD1RC0LD1LA1RE0LF0LA0RB1RA---0RC",
40:"1RB1LD1RC0LD1LA1RE1LF0LA0RB1RA---0LE",
41:"1RB1LD1RC0LD1LA1RE1LF0LA0RB1RA---1RB",
140:"1RB1LD1RC0LD1LA1RE0LD0LA0RB1RF1RB---",
148:"1RB1LD1RC0LD1LA1RE0LD0LA0RB1RF1RE---"}
def infer(i):
 t=TABLES[i];P='010';pre='10';D=['100','000','110','010'];E=['11','01']
 if i in (20,148):D=['010','000','011','001'];E=['011','001']
 F=lambda w:C(0,W(''),w)
 def f(x,k,inc):
  d=D[0] if inc else D[-1];v=W(pre+d,d,1,x) if k else W(pre+x)
  return F(W(P*(1+inc),P,0,v))
 out={};seed=(0,'','');j=0
 while seed!=(0,'',P+pre+E[0]):seed=step(t,seed);j+=1;assert j<500
 for name,x,y,prot in [(f'd{j}',D[j],D[j+1],True) for j in range(3)]+[('t0',E[0],E[1],False),('t1',E[1],D[0]+E[0],False)]:
  for k in (0,1):
   z,g=f(x,k,0),f(y,k,1)
   rr=prove(t,z,g,protected=prot);assert rr,(i,name,k)
   out[name+str(k)]=rr
 return dict(table=t,entry=j,macros=out,digits=D,terms=E)
def emit(d,ns,output):
 from emitUnaryBank import macro2
 from emitRadixMarkerBank import fn
 from emitauto import machine,bits
 name='BB6Coverage.Agent31Pump.Auto2.GrowRadix.'+ns
 s=['import Agent46GrowRadixCheck','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace '+name,'open BB6Coverage Agent31Pump Auto2 GrowRadix',machine(0,d['table']).replace('def p0 ', 'def p ',1),fn('digit',d['digits']),f'def terminal (b : Bool) : List Bool := if b then {bits(d["terms"][1])} else {bits(d["terms"][0])}']
 for k,j in [('normalZ',0),('normalS',1)]:
  s.append(f'def {k} : Fin 3 → Macro := fun i => match i.val with\n'+''.join(f'  | {i} => {macro2(d["macros"][f"d{i}{j}"])}\n' for i in range(2))+'  | _ => '+macro2(d['macros'][f'd2{j}']))
 for k,j in [('terminalZ',0),('terminalS',1)]:
  s.append(f'def {k} (b : Bool) : Macro := if b then {macro2(d["macros"][f"t1{j}"])} else {macro2(d["macros"][f"t0{j}"])}')
 s.extend([f'def cert : GrowRadix.Cert := ⟨⟨digit,terminal⟩,{d["entry"]},normalZ,normalS,terminalZ,terminalS⟩','theorem checked : Checked p cert := by constructor <;> decide','theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := GrowRadix.never p cert checked m hm','#print axioms never','end '+name,''])
 Path(output).write_text('\n'.join(s))
if __name__=='__main__':
 cache=Path('growradix-bank.json')
 existing={d['table']:d for d in json.loads(cache.read_text())} if cache.exists() else {}
 bank=[]
 for i in map(int,sys.argv[1:] or list(TABLES)):
  d=existing.get(TABLES[i]) or infer(i)
  bank.append(d);emit(d,f'Leaf{i}',f'GrowRadix{i}.lean')
 if not sys.argv[1:]:
  cache.write_text(json.dumps(bank,separators=(',',':'))+'\n')
