from dataclasses import dataclass
from itertools import product
from pathlib import Path
from collections import Counter
import json,sys,re
def parse(s):
 return [s.replace("_", "")[i:i+3] for i in range(0,36,3)]

@dataclass(frozen=True)
class Z:
 q:int;l:str;r:str

def bit(w):
 if not w:return '0'
 if w[0] not in '01':raise ValueError('opaque')
 return w[0]

def step(p,z):
 a=p[2*z.q+int(bit(z.l))]
 if a=='---':raise ValueError('hole')
 w,d,q=a;q=ord(q)-65
 if d=='R':return Z(q,bit(z.r)+w+z.l[1:],z.r[1:]),1
 return Z(q,z.l[1:],w+z.r),-1

def exit_left(p,q,k,s,limit=30000):
 z=Z(q,'1L','1'*(k-1)+s+'R');h=0
 try:
  for t in range(1,limit+1):
   z,d=step(p,z);h+=d
   if h<0:return t,z
 except ValueError:pass
 return None

def walk(p,z,target,core=None,limit=1000):
 # Macros require the same restored unary block, exact arbitrary tails.
 actions=[];start=z;steps=0;seen=set()
 for _ in range(limit):
  if z==target:
   if steps:actions.append(('steps',steps,start,z))
   return actions
  if z in seen:return None
  seen.add(z)
  if core:
   q,k,s,qout=core;prefix='1'*(k-1)+'X'+s
   if z.q==q and z.l.startswith('1') and z.r.startswith(prefix):
    new=Z(qout,z.l[1:],'1'+z.r)
    if steps:actions.append(('steps',steps,start,z))
    actions.append(('ih',0,z,new));z=start=new;steps=0;continue
  try:z,_=step(p,z);steps+=1
  except ValueError:return None
 return None

def core_candidates(p,period,s):
 for q in range(6):
  for k in range(1,6):
   a=exit_left(p,q,k,s)
   if not a:continue
   basecost,z=a
   if z.l!='L' or z.r!='1'*k+s+'R':continue
   qout=z.q
   # Finite recursive base and one successor algebraic pattern, never empirical extrapolation.
   core=(q,k,s,qout)
   start=Z(q,'1L','1'*(k+period-1)+'X'+s+'R')
   target=Z(qout,'L','1'*(k+period)+'X'+s+'R')
   acts=walk(p,start,target,core)
   if not acts:continue
   m=sum(a[0]=='ih' for a in acts);c=sum(a[1] for a in acts)
   if m<1 or c<1:continue
   yield core,basecost,m,c,acts

def boundary(p,limit=100000,maxevents=35):
 z=Z(0,'','');h=lo=hi=0;events=[]
 for t in range(limit):
  if h<lo:
   lo=h
   if z.l=='':events.append((t,z))
   if len(events)>=maxevents:break
  try:z,d=step(p,z);h+=d
  except ValueError:break
 return events

def families(p):
 ev=boundary(p)
 for t,z in ev:
  m=re.match(r'^(0*)(1+)(0+1+[01]*)$',z.r)
  if not m:continue
  pre,ones,suf=m.groups();k=len(ones)
  for u,y in ev:
   if u<=t or y.q!=z.q:continue
   m2=re.match(r'^(0*)(1+)(0+1+[01]*)$',y.r)
   if not m2:continue
   pre2,ones2,suf2=m2.groups();period=len(ones2)-k
   if pre2!=pre or suf2!=suf or not 1<=period<=5:continue
   yield t,z.q,pre,k,suf,period

def find(p):
 cache={}
 for entry,q,pre,k,suf,period in families(p):
  for sl in range(2,len(suf)+1):
   s=suf[:sl]
   if not re.match(r'^0+1+$',s):continue
   key=period,s
   if key not in cache:cache[key]=list(core_candidates(p,period,s))
   for core,b,m,c,acts in cache[key]:
    start=Z(q,'',pre+'1'*k+'X'+suf)
    target=Z(q,'',pre+'1'*(k+period)+'X'+suf)
    outer=walk(p,start,target,core,limit=1000)
    if outer and any(a[0]=='ih' for a in outer):return (entry,q,pre,k,suf,period),core,b,m,c,acts,outer
 return None

def word(w,period):
 # All opaque tokens are list chunks; fixed bits preceding X are consed.
 # Right tail R and left tail L may be empty lists or arbitrary variables.
 if not w:return '[]'
 if w[0] in '01':return ('true' if w[0]=='1' else 'false')+'::'+word(w[1:],period)
 if w[0]=='X':return f'(O ({period}*n)++{word(w[1:],period)})'
 if w in ('L','R'):return w
 raise ValueError(w)

def cfg(z,period):return f'⟨{z.q},{word(z.l,period)},{word(z.r,period)}⟩'

def tabledef(p):
 lines=[]
 for i,a in enumerate(p):
  if a=='---':continue
  lines.append(f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(a[0]=="1").lower()},{str(a[1]=="R").lower()},{ord(a[2])-65}⟩)')
 return 'def table : PartialMachine := fun s => match s.1.val,s.2 with\n'+'\n'.join(lines)+'\n  | _,_ => none\n'

def emit_action(a,i,p,core,period,ih):
 kind,count,start,end=a
 if kind=='steps':return f'    have h{i} : run0 table {count} {cfg(start,period)} = some {cfg(end,period)} := by rfl'
 q,k,s,qout=core
 prefix='1'*(k-1)+'X'+s
 assert start.r.startswith(prefix)
 L=start.l[1:];R=start.r[len(prefix):]
 if ih:return f'    have h{i} := ih ({word(L,period)}) ({word(R,period)})'
 return f'    have h{i} := core n ({word(L,period)}) ({word(R,period)})'

def proof_actions(actions,period,core,ih=True,indent='    '):
 out=[]
 for i,a in enumerate(actions):out.append(emit_action(a,i,None,core,period,ih))
 join='h0'
 for i in range(1,len(actions)):join=f'join0 ({join}) h{i}'
 out.append(f'    have H := {join}')
 ct='+'.join('T n' if a[0]=='ih' else str(a[1]) for a in actions)
 return out,ct

def generate(branch,i,s,res):
 (entry,q,pre,k,suf,period),core,b,m,c,acts,outer=res
 cq,ck,cs,cqo=core
 ns=f'BB6.Agent3Raw120Auto{branch}.M{i}'
 out=['import SweepPumping','set_option maxRecDepth 40000','set_option maxHeartbeats 4000000',f'namespace {ns}','open BB6Coverage BB6Coverage.Agent31Pump','',f'/-- {s}; recursive local unary shuttle. -/',tabledef(parse(s)),'abbrev O (n : Nat) := List.replicate n true',f'def T : Nat → Nat | 0 => {b} | n+1 => {m}*T n+{c}','']
 # Explicit fixed prefix, then O(period*n), then sentinel.
 st=Z(cq,'1L','1'*(ck-1)+'X'+cs+'R');en=Z(cqo,'L','1'*ck+'X'+cs+'R')
 out+=[f'theorem core (n : Nat) (L R : List Bool) : run0 table (T n) {cfg(st,period)} = some {cfg(en,period)} := by','  induction n generalizing L R with','  | zero => rfl','  | succ n ih =>',f'    rw [show {period}*(n+1)={period}*n'+('+1'*period)+' by omega]','    simp only [List.replicate_succ,List.cons_append]']
 ac,ct=proof_actions(acts,period,core);out+=ac
 out+=[f'    rw [show {ct}=T (n+1) by simp [T]; omega] at H','    exact H','']
 st=Z(q,'',pre+'1'*k+'X'+suf);en=Z(q,'',pre+'1'*(k+period)+'X'+suf)
 out+=[f'def family (n : Nat) : Z0 := {cfg(st,period)}',f'theorem entry : run0 table {entry} ⟨0,[],[]⟩ = some (family 0) := by rfl']
 om=sum(a[0]=='ih' for a in outer);oc=sum(a[1] for a in outer);cost=f'{om}*T n+{oc}'
 out+=[f'theorem growth (n : Nat) : run0 table ({cost}) (family n) = some (family (n+1)) := by']
 ac,ct=proof_actions(outer,period,core,False);out += [x[2:] for x in ac]
 out+=[f'  rw [show {ct}={cost} by omega] at H','  unfold family',f'  rw [show {period}*(n+1)={period}*n'+('+1'*period)+' by omega]','  exact H',f'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := never_of_growth table family {entry} (fun n => {cost}) entry (by intro n; omega) growth m hm','#print axioms never',f'end {ns}','']
 return '\n'.join(out),ns

def main():
 """Generate one module from an explicit JSON list of [index,table] pairs."""
 branch, input_path, output_path = sys.argv[1:]
 result=[]; header=['import SweepPumping','set_option maxRecDepth 40000','set_option maxHeartbeats 4000000','']
 for i,s in sorted(json.loads(Path(input_path).read_text())):
  ans=find(parse(s))
  if not ans:raise RuntimeError(f'No recursive shuttle for {i}: {s}')
  code,ns=generate(branch,i,s,ans)
  result.append('\n'.join(code.splitlines()[3:])+'\n')
  print(i,ns,ans[:5])
 Path(output_path).write_text('\n'.join(header)+ '\n' + '\n'.join(result))
if __name__=='__main__':main()
