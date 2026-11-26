from collections import Counter,deque
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
import argparse
TBL=[7,17,11,5,14,8,24,16,23,11,3,17]
def word(ns):return ''.join(('1' if n>0 else '0')*abs(n) for n in ns)
P=word([-1,2,-1,2,-1,2,-2,3,-1,7,-1,2,-5,3]); M0=word([-1,1,-1,4,-1,6,-2,3]); M1=word([-1,7,-1,4,-1,6,-2,3]); U=M1+M0*5;Q='01111101111';K='0111111'
def raw(q,l,r,n,guard=False):
 l,r=deque(map(int,l)),deque(map(int,r))
 for _ in range(n):
  assert r or not guard
  a=r.popleft() if r else 0;v=TBL[2*q+a];assert v!=24
  w=v>>1&1
  if v&1:l.appendleft(w)
  else:
   assert l or not guard
   r.appendleft(w);r.appendleft(l.popleft() if l else 0)
  q=v>>2
 return q,''.join(map(str,l)),''.join(map(str,r))
def macro(l,r):
 if r.startswith('01'):return '', '01','01','',2
 if r.startswith('001'):return '', '001','011','',3
 if r.startswith('10'):
  a=l[0] if l else '0';return a,'10','',a+'01',3
 if r.startswith('11'):
  a=(l+'000')[:3];assert a.startswith('01');return a,'11','',a[-1]+'0100',5
 assert r.startswith('000')
 n=0
 while 3+n<len(r) and r[3+n]=='1':n+=1
 gap=r[3+n:5+n]
 if gap=='00':
  if n==0:return '','00000','11','101',6
  return '', '000'+'1'*n+'00','0'*(n-1)+'111','001',n+6
 assert gap=='01'
 if n==0:
  a=(l+'000')[:3];assert a.startswith('01');return a,'00001','',a[-1]+'0100000',11
 if n==1:return '','000101','1','10100',9
 raise ValueError(('D0',l,r))
@dataclass(frozen=True)
class Rep:w:str;v:str

def norm(xs):
 out=[]
 for x in xs:
  if isinstance(x,str):
   if not x:continue
   if out and isinstance(out[-1],str):out[-1]+=x
   else:out.append(x)
  else:out.append(x)
 if out and isinstance(out[-1],str):
  out[-1]=out[-1].rstrip('0')
  if not out[-1]:out.pop()
 return out

def literal(xs):return ''.join(x for x in xs if isinstance(x,str))
def pref(xs,n=100000):
 if not xs:return '0'*min(n,100)
 if isinstance(xs[0],Rep):return ''
 if len(xs)==1:return (xs[0]+'0'*min(n,100))[:n]
 return xs[0][:n]
def split(xs):
 if not xs:return '',None,[]
 if isinstance(xs[0],Rep):return '',xs[0],xs[1:]
 if len(xs)==1:return xs[0],None,[]
 return xs[0],xs[1],xs[2:]
def consume(xs,w,out):
 a,m,rest=split(xs)
 if m is None:
  assert (a+'0'*len(w)).startswith(w);return norm([out+a[len(w):]])
 assert a.startswith(w);return norm([out+a[len(w):],m,*rest])
def guarded(l,r):
 try:a,b,c,d,t=macro(l,r)
 except (AssertionError,IndexError,ValueError):return None
 if not l.startswith(a) or not r.startswith(b):return None
 return a,b,c,d,t
cache={};failcache=set();loopdata={}
def findloop(side,A,W,C,limit=3000):
 key=(side,A,W,C[:256]);C=C[:256]
 if key in cache:return cache[key]
 if key in failcache:return None
 l,r=(A+W,C) if side==0 else (C,A+W)
 consumed=0;generated=0;cost=0;trace=[]
 for i in range(limit):
  h=guarded(l,r)
  if h is None:break
  a,b,c,d,dt=h;trace.append(h)
  take,give=(len(b),len(d)) if side==0 else (len(a),len(c))
  consumed+=max(0,take-generated);generated=max(0,generated-take)+give
  l=c+l[len(a):];r=d+r[len(b):];cost+=dt
  s,o=(l,r) if side==0 else (r,l)
  if s==A:
   fixed=C[:consumed];tail=C[consumed:];assert o[generated:]==tail
   if o[:generated].startswith(fixed):
    V=o[len(fixed):generated];ans=(fixed,V,cost,i+1);cache[key]=ans
    src=(A+W,fixed) if side==0 else (fixed,A+W);dst=(A,fixed+V) if side==0 else (fixed+V,A)
    assert raw(4,*src,cost,True)==(4,*dst);loopdata[(side,A,W,fixed,V,cost)]=trace.copy();return ans
  if len(l)+len(r)>len(A+W+C)+1024:break
 failcache.add(key);return None

def rotations(xs):
 A,m,tail=split(xs);assert m is not None;W=m.w
 yield xs,0
 for i in range(1,min(len(A),len(W))+1):
  if A[-i:]==W[-i:]:yield norm([A[:-i],Rep(W[-i:]+W[:-i],m.v),W[-i:],*tail]),-i
 D,n,rest=split(tail)
 for i in range(1,len(W)+1):
  d=D+'0'*i if n is None else D
  if d[:i]==W[:i]:yield norm([A+W[:i],Rep(W[i:]+W[:i],m.v),D[i:],*([n,*rest] if n is not None else [])]),i
  else:break

def transfer(L,R,side):
 S,O=(L,R) if side==0 else (R,L);C=pref(O,256)
 best=None
 for SS,rot in rotations(S):
  A,m,T=split(SS);W=m.w
  k=0
  while A.endswith(W):A=A[:-len(W)];k+=1
  D,n,rest=split(T)
  while D.startswith(W):D=D[len(W):];k+=1
  T=norm([D,*([n,*rest] if n is not None else [])])
  if len(A)>64:continue
  res=findloop(side,A,W,C)
  if res is None:continue
  fixed,V,cost,n=res
  if best is None or k>best[0]:best=(k,A,m,T,fixed,V,cost,n,rot)
  if k>0:break
 if best is None:return None
 k,A,m,T,fixed,V,cost,n,rot=best
 OS=consume(O,fixed,fixed);a,b,c=split(OS)
 assert a.startswith(fixed) or b is None and (a+'0'*len(fixed)).startswith(fixed)
 after=norm([a[len(fixed):],*([b,*c] if b is not None else [])]);newO=norm([fixed+V*k,*([Rep(V,m.v)] if V else []),*after]);newS=norm([A,*T])
 return (newS,newO,m.v,cost,n,(side,A,m.w,fixed,V,cost,rot,k),T,after) if side==0 else (newO,newS,m.v,cost,n,(side,A,m.w,fixed,V,cost,rot,k),after,T)

def common_rotation(S,w):
 for SS,rot in rotations(S):
  if rot and pref(SS,len(w)).startswith(w):return SS,rot
 return None

def sweep(L,R):
 A=split(L)[0];C=split(R)[0]
 if A.startswith('1111110') and C.startswith('101'):
  n=0
  while A.startswith('1111110',7*n):n+=1
  return consume(L,'1111110'*n,''),consume(R,'101','101'+'0011111'*n),29*n,n,(0,'','1111110','101','0011111',29)
 if C.startswith('00110011111'):
  n=0
  while C.startswith('0011111',4+7*n):n+=1
  return consume(L,'',K*n),consume(R,'0011'+'0011111'*n,'0011'),19*n,n,(1,'0011','0011111','',K,19)
 return None

# Exact repeated-prefix transfers on concrete literals, learned from guarded loops.
# Index by side and first eight bits of consumed source (short keys separately).
bank={};newattempt=set();hits=Counter();miss=Counter()
def register(info):
 side,A,W,C,V,cost=info
 key=(side,(A+W)[:8]);bank.setdefault(key,set()).add(info)

def concrete(L,R):
 best=None
 for side,S,O in [(0,L,R),(1,R,L)]:
  s=split(S)[0];c=pref(O,256)
  # Existing exact guarded rules.
  for d in range(1,min(8,len(s))+1):
   for info in sorted(bank.get((side,s[:d]),())):
    _,A,W,C,V,cost=info
    if not s.startswith(A+W+W) or not c.startswith(C):continue
    n=2
    while s.startswith(W,len(A)+n*len(W)):n+=1
    gain=n*cost
    if best is None or gain>best[0]:best=(gain,info,n)
  if best is not None and best[0]>=100:continue
  # Discover a transfer when a substantial concrete periodic prefix exists.
  # Only search a few smallest primitive periods for each prefix offset.
  for a in range(min(5,len(s))):
   for d in range(1,min(32,(len(s)-a)//2)+1):
    W=s[a:a+d]
    if not s.startswith(W,a+d):continue
    n=2
    while s.startswith(W,a+n*d):n+=1
    if n<3 or n*d<12:continue
    A=s[:a];key=(side,A,W,c[:32])
    if key in newattempt:continue
    newattempt.add(key)
    res=findloop(side,A,W,c,limit=300)
    if res is None:continue
    C,V,cost,_=res;info=(side,A,W,C,V,cost);register(info)
    gain=n*cost
    if best is None or gain>best[0]:best=(gain,info,n)
    if gain>=100:break
   if best is not None and best[0]>=100:break
 if best is None or best[0]<12:return None
 gain,info,n=best;side,A,W,C,V,cost=info
 S,O=(L,R) if side==0 else (R,L)
 S=consume(S,A+W*n,A);O=consume(O,C,C+V*n)
 hits[info]+=1
 return (S,O,gain,n,info) if side==0 else (O,S,gain,n,info)


# Untrusted discovery; Lean checks all emitted proof data.
def val(w):return int(w[::-1] or '0',2)
def inst(xs,x,y):return ''.join(w if isinstance(w,str) else w.w*(x if w.v=='X' else y) for w in xs)
def samples(L,R):return tuple((val(inst(L,x,y)),val(inst(R,x,y))) for x,y in ((0,0),(1,0),(0,1),(1,1)))
def wordlean(w):return f'⟨{len(w)},{val(w)}⟩'
def symlean(ws):return '['+','.join('.lit '+wordlean(w) if isinstance(w,str) else '.rep '+wordlean(w.w)+' '+str(w.v=='Y').lower() for w in ws)+']'
def statelean(LR):return '⟨'+symlean(LR[0])+','+symlean(LR[1])+'⟩'
def costlean(c):return f'⟨{c[0]},{c[1]},{c[2]}⟩'
def addcost(a,b):return tuple(x+y for x,y in zip(a,b))
def sidecompose(a,b,c,d):
 if c.startswith(b):return a+c[len(b):],d
 if b.startswith(c):return a,d+b[len(c):]
 return None

def compose(r,s):
 a,b,c,d,t=r;A,B,C,D,T=s
 l=sidecompose(a,c,A,C);rr=sidecompose(b,d,B,D)
 if l is None or rr is None:return None
 return l[0],rr[0],l[1],rr[1],t+T

def fixed(info,n):
 side,A,W,C,V,t=info
 return (A+W*n,C,A,C+V*n,t*n) if side==0 else (C,A+W*n,C+V*n,A,t*n)

class Builder:
 def __init__(self):self.rules={};self.sweeps={};self.traces={};self.pending=[];self.combined=('','','','',0);self.start=None
 def rule(self,r):
  if r not in self.rules:self.rules[r]=f'r{len(self.rules)}'
  return self.rules[r]
 def sweep(self,s):
  if s not in self.sweeps:self.sweeps[s]=f's{len(self.sweeps)}'
  return self.sweeps[s]
 def begin(self,name,L,R):
  self.name=name;self.initial=(L,R);self.current=(L,R);self.events=[];self.pending=[];self.combined=('','','','',0);self.start=None
 def emit(self,a,LR,cost):
  self.events.append((a,LR,cost));self.current=LR
 def flush(self):
  if not self.pending:return
  a,b,c,d,t=self.combined;L,R=self.start;out=self.current
  Lt=consume(L,a,'');Rt=consume(R,b,'')
  assert samples([a,*Lt],[b,*Rt])==samples(L,R),('fixed source',a,b,L,R)
  assert samples([c,*Lt],[d,*Rt])==samples(*out),('fixed target',a,b,c,d)
  self.emit('.fixed ['+','.join(self.pending)+'] '+symlean(Lt)+' '+symlean(Rt),out,(t,0,0))
  self.pending=[];self.combined=('','','','',0);self.start=None
 def fixed(self,r,LR,info=None,n=None):
  c=compose(self.combined,r)
  if c is not None and self.pending:
   try:consume(self.start[0],c[0],'');consume(self.start[1],c[1],'')
   except AssertionError:c=None
  if c is None or len(self.pending)>=64:
   self.flush();c=r
  if not self.pending:self.start=self.current
  self.pending.append(self.rule(r) if info is None else f'({self.sweep(info)}.fixed {n})')
  self.combined=c;self.current=LR
 def variable(self,info,v,L,R,LR):
  self.flush();side,A,W,C,V,t,rot,k=info
  src=([A,W*k,Rep(W,v),*L],[C,*R]) if side==0 else ([C,*L],[A,W*k,Rep(W,v),*R])
  dst=([A,*L],[C,V*k,Rep(V,v),*R]) if side==0 else ([C,V*k,Rep(V,v),*L],[A,*R])
  assert samples(*src)==samples(*self.current),('variable source',info)
  assert samples(*dst)==samples(*LR),('variable target',info)
  self.emit(f'.symbolic {self.sweep(info[:6])} {str(v=="Y").lower()} {k} {symlean(L)} {symlean(R)}',LR,(t*k,t if v=='X' else 0,t if v=='Y' else 0))
 def finish(self,expected):
  self.flush();assert samples(*self.current)==samples(*expected)
  self.traces[self.name]=(self.initial,self.events,expected)
  print(self.name,'events',len(self.events),'rules',len(self.rules),'sweeps',len(self.sweeps),flush=True)

def period(b):
 L=norm([P+M0,Rep(U,'X'),M1+M0*6+Q,Rep(K,'Y')]);R=[];expected=norm([P+M0+U,Rep(U,'X'),M1+M0*6+Q+K*553,Rep(K,'Y')]);b.begin('period',L,R)
 cost=Counter();cleans=0;i=0;count=Counter()
 while cleans<145:
  i+=1;s=sweep(L,R) or concrete(L,R)
  if s:
   L,R,dt,n,info=s;cost['c']+=dt;count['sweep']+=1;b.fixed(fixed(info,n),(L,R),info,n)
  else:
   l,r=literal(L),literal(R);a,c,e,f,dt=macro(l+'000',r+'00000');touched=[]
   if not pref(L,len(a)).startswith(a):touched.append(0)
   if not pref(R,len(c)).startswith(c):touched.append(1)
   if touched:
    success=False
    for side in touched:
     h=transfer(L,R,side)
     if h:
      L,R,v,dc,n,info,Lt,Rt=h;cost[v]+=dc;cost['c']+=dc*info[-1];register(info[:6]);b.variable(info,v,Lt,Rt,(L,R));success=True;count['transfer']+=1;break
    if success:continue
    raise AssertionError(('symbolic stuck',i,cleans,touched))
   L=consume(L,a,e);R=consume(R,c,f);cost['c']+=dt;count['macro']+=1;b.fixed((a,c,e,f,dt),(L,R))
  if not R:cleans+=1
 assert not R and cleans==145 and cost=={'c':24481769,'X':1294020,'Y':79632},cost
 b.finish((expected,[]));print('period cost',cost,'actions',count,flush=True)

def seed(b):
 L,R=[],['101'];b.begin('seed',L,R);t=4;goal=28792194
 while t<goal:
  s=sweep(L,R) or concrete(L,R)
  if s and t+s[2]<=goal:
   L,R,dt,n,info=s;b.fixed(fixed(info,n),(L,R),info,n)
  else:
   a,c,e,f,dt=macro(literal(L)+'000',literal(R)+'00000')
   L=consume(L,a,e);R=consume(R,c,f);b.fixed((a,c,e,f,dt),(L,R))
  t+=dt
 assert t==goal,(t,goal)
 expected=[P+M0+M1+M0*6+Q+K*619]
 b.finish((expected,[]));print('seed cost',t,flush=True)

def generate(b,out,chunk=24):
 out.mkdir(parents=True,exist_ok=True)
 header='import SymTrace\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\nnamespace BB6.Agent6RF4563\nopen BB6Coverage BB6.Agent6NatTape BB6.Agent6WordNat BB6.Agent6SymWord BB6.Agent6RuleCompose BB6.Agent6SymTrace\n'
 table='def p : PartialMachine := fun (q,b) => match q.val,b with\n'+''.join(f'  | {i//2}, {str(bool(i%2)).lower()} => some (some ⟨{str(bool(v&2)).lower()},{str(bool(v&1)).lower()},{v//4}⟩)\n' for i,v in enumerate(TBL) if v!=24)+'  | _, _ => none\n'
 base=header+table+f'def widths : Widths := ⟨{len(U)},{len(K)}⟩\n'
 for r,name in b.rules.items():
  a,c,e,f,t=r;base+=f'def {name}d : Rule := ⟨{wordlean(a)},{wordlean(c)},{wordlean(e)},{wordlean(f)},{t}⟩\ndef {name} : CR p := CR.checked p {name}d (by decide +kernel)\n'
 for s,name in b.sweeps.items():
  side,A,W,C,V,t=s;base+=f'def {name}d : Sweep := ⟨{str(side==0).lower()},{wordlean(A)},{wordlean(W)},{wordlean(C)},{wordlean(V)},{t}⟩\ndef {name} : CS p := CS.checked p {name}d (by decide +kernel)\n'
 for name,(initial,events,expected) in b.traces.items():base+=f'def {name}Start : State := {statelean(initial)}\ndef {name}End : State := {statelean(expected)}\n'
 (out/'RF4563Base.lean').write_text(base+'end BB6.Agent6RF4563\n')
 modules=[];sums={}
 for name,(initial,events,expected) in b.traces.items():
  total=(0,0,0);parts=[];prev=initial
  for i in range(0,len(events),chunk):
   es=events[i:i+chunk];n=i//chunk;end=es[-1][1] if i+chunk<len(events) else expected;c=(0,0,0)
   for a,_,k in es:c=addcost(c,k)
   total=addcost(total,c);mod=f'RF4563{name.title()}{n:04d}';prefix=f'{name}{n}'
   txt=header.replace('import SymTrace','import RF4563Base')
   txt+=f'def {prefix}Start : State := {statelean(prev)}\ndef {prefix}End : State := {statelean(end)}\ndef {prefix}Actions : List (Action p) := [\n'+',\n'.join(a for a,_,_ in es)+'\n]\n'
   txt+=f'theorem {prefix}Run (x y : Nat) : runN p (({costlean(c)} : Cost).eval x y) ({prefix}Start.eval x y) = some ({prefix}End.eval x y) := check_sound widths {prefix}Start {prefix}Actions {prefix}End {costlean(c)} (by decide +kernel) x y\n#print axioms {prefix}Run\nend BB6.Agent6RF4563\n'
   (out/(mod+'.lean')).write_text(txt);modules.append(mod);parts.append((prefix,c));prev=end
  sums[name]=(total,parts)
 txt=''.join('import '+m+'\n' for m in modules)+header[header.index('set_option'):]
 for name,(total,parts) in sums.items():
  layer=[(pr+'Run',pr+'Start',pr+'End',c) for pr,c in parts];depth=0
  while len(layer)>1:
   new=[]
   for i in range(0,len(layer),2):
    if i+1==len(layer):new.append(layer[i]);continue
    th1,src,mid,c1=layer[i];th2,mid2,dst,c2=layer[i+1];c=addcost(c1,c2);th=f'{name}J{depth}_{i//2}'
    txt+=f'theorem {th} (x y : Nat) : runN p (({costlean(c)} : Cost).eval x y) ({src}.eval x y) = some ({dst}.eval x y) := by\n  have H := runN_join ({th1} x y) ({th2} x y)\n  have hc : (({costlean(c1)} : Cost).eval x y)+(({costlean(c2)} : Cost).eval x y) = (({costlean(c)} : Cost).eval x y) := by simp only [Cost.eval]; omega\n  rw [hc] at H\n  exact H\n'
    new.append((th,src,dst,c))
   layer=new;depth+=1
  th,src,dst,c=layer[0];assert c==total
  txt+=f'theorem {name}Run (x y : Nat) : runN p (({costlean(c)} : Cost).eval x y) ({name}Start.eval x y) = some ({name}End.eval x y) := {th} x y\n#print axioms {name}Run\n'
 txt+='end BB6.Agent6RF4563\n';(out/'RF4563Join.lean').write_text(txt)
 print('generated',len(modules),'modules',sum(p.stat().st_size for p in out.glob('*.lean')),'bytes',flush=True)

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('out',type=Path);ap.add_argument('--period-only',action='store_true');ap.add_argument('--chunk',type=int,default=24);a=ap.parse_args();b=Builder();period(b)
 if not a.period_only:seed(b)
 generate(b,a.out,a.chunk)
