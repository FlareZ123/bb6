"""Untrusted compact sweep-certificate replay. Every emitted finite step and
arbitrary-tail block transfer is checked by Lean; the generator is not trusted.
Recipe JSONL: [id, table, entry, state, left, right, actions]. A tape expression
is constant|repeat|constant|...|constant. A fixed action is a positive integer
step count; a sweep is [side, source-prefix-len, dest-prefix-len, output, steps].
side=0 moves left; side=1 moves right. All repeated words share parameter n.
"""
from pathlib import Path
import json,sys

def lit(s):return '['+','.join('true' if c=='1' else 'false' for c in s)+']'
def expr(s):return ' ++ '.join(lit(x) if i%2==0 else f'rep {lit(x)} n' for i,x in enumerate(s) if x) or '[]'
def ze(z):return f'⟨{z[0]}, {expr(z[1])}, {expr(z[2])}⟩'
def tape(s):
 a=s.split('|')
 if len(a)==3 and not a[1]:a=[a[0]+a[2]]
 assert len(a)%2 and all(a[i] for i in range(1,len(a),2))
 return a

def table(s):
 out=['def table : PartialMachine := fun s =>','  match s.1.val,s.2 with']
 for i in range(12):
  a=s[3*i:3*i+3]
  if a!='---':out.append(f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(a[0]=="1").lower()},{str(a[1]=="R").lower()},{ord(a[2])-65}⟩)')
 return '\n'.join(out+['  | _,_ => none'])
def head(a):
 if a[0]:return a[0][0]
 assert len(a)==1,'unproved read through repetition'
 return '0'
def tail(a):
 if not a[0]:assert len(a)==1,'unproved pop through repetition'
 return [a[0][1:]]+a[1:]
def pre(s,a):return [s+a[0]]+a[1:]
def step(p,z):
 q,l,r=z;a=p[2*q+int(head(l))];assert a!='---'
 q=ord(a[2])-65
 return (q,pre(head(r)+a[0],tail(l)),tail(r)) if a[1]=='R' else (q,tail(l),pre(a[0],r))

def equal_transforms(a,b):
 a=a.copy();trs=[];assert len(a)==len(b)
 for i in range(0,len(a)-1,2):
  x,w,t=a[i:i+3];y,v=b[i:i+2];assert len(w)==len(v);old=a.copy()
  if len(x)>=len(y):
   assert x.startswith(y);d=x[len(y):];assert d+w==v+d
   if not d:continue
   a[i:i+3]=[y,v,d+t];rev=False
  else:
   assert y.startswith(x);d=y[len(x):];assert t.startswith(d) and w+d==d+v
   a[i:i+3]=[y,v,t[len(d):]];rev=True;w,v=v,w
  trs.append((old,a.copy(),i,d,w,v,rev))
 assert a==b
 return trs

def emit(rec):
 i,s,t,q,l,r,actions=rec;p=[s[j:j+3] for j in range(0,36,3)];start=(q,tape(l),tape(r));z=start
 out=[f'namespace M{i}',table(s),f'def family (n : Nat) : Z0 := {ze(z)}',f'theorem entry : run0 table {t} ⟨0,[],[]⟩ = some (family 0) := by rfl']
 c0=c1=0;costs=[]
 for j,act in enumerate(actions):
  if isinstance(act,int):
   assert act>0;z1=z
   for _ in range(act):z1=step(p,z1)
   c0+=act;costs.append(str(act));out.append(f'theorem h{j} (n : Nat) : run0 table {act} {ze(z)} = some {ze(z1)} := by rfl')
  else:
   side,apl,bpl,o,k=act;q,l,r=z;a,b=(l,r) if side==0 else (r,l);ap,w,*at=a;assert len(ap)==apl
   bp,bt=b[0][:bpl],[b[0][bpl:]]+b[1:];assert len(bp)==bpl and len(w)==len(o) and k>0
   aa=pre(ap,at);bb=[bp,o]+bt;z1=(q,aa,bb) if side==0 else (q,bb,aa)
   lp,rp=(ap,bp) if side==0 else (bp,ap);L,R=(at,bt) if side==0 else (bt,at);l0,r0,I,O=map(lit,(lp,rp,w,o))
   if side==0:src=f'⟨{q}, {l0} ++ {I} ++ L, {r0} ++ R⟩';dst=f'⟨{q}, {l0} ++ L, {r0} ++ {O} ++ R⟩';fn='sweepL'
   else:src=f'⟨{q}, {l0} ++ L, {r0} ++ {I} ++ R⟩';dst=f'⟨{q}, {l0} ++ {O} ++ L, {r0} ++ R⟩';fn='sweepR'
   c1+=k;costs.append(f'{k}*n');out.append(f'theorem one{j} (L R : List Bool) : run0 table {k} {src} = some {dst} := by rfl')
   out.append(f'theorem h{j} (n : Nat) : run0 table ({k}*n) {ze(z)} = some {ze(z1)} := by\n  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using ({fn} table {q} {l0} {r0} {I} {O} {k} one{j} n ({expr(L)}) ({expr(R)}))')
  z=z1
 goal=(start[0],*[ [x+(a[j+1] if j+1<len(a) else '') if j%2==0 else x for j,x in enumerate(a)] for a in start[1:]])
 assert z[0]==goal[0]
 out.append(f'theorem endEq (n : Nat) : ({ze(z)} : Z0) = family (n+1) := by\n  have hg : family (n+1) = ({ze(goal)} : Z0) := by simp only [family,rep,List.append_assoc,List.cons_append] <;> rfl\n  rw [hg]')
 hs=[]
 for j,(a,b) in enumerate(zip(z[1:],goal[1:])):
  if a==b:continue
  hn='hl' if j==0 else 'hr';hs.append(hn);out.append(f'  have {hn} : {expr(a)} = {expr(b)} := by')
  trs=equal_transforms(a,b)
  if not trs:out.append('    rfl');continue
  names=[]
  for ti,(old,new,k,d,w,v,rev) in enumerate(trs):
   name=f'{hn}{ti}';names.append(name);out.append(f'    have {name} : {expr(old)} = {expr(new)} := by');a,b=old,new
   if rev:a,b=new,old;out.append('      symm')
   prefix=expr(a[:k]+[b[k]]);suffix=expr(a[k+2:]);out.append(f'      simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (commute_context ({prefix}) ({suffix}) {lit(d)} {lit(w)} {lit(v)} (by decide) n)')
  out.append('    exact '+names[0]+''.join(f'.trans {name}' for name in names[1:]))

 if hs:out.append('  rw ['+','.join(hs)+']')
 # rw may close the goal if all components syntactically agree.
 cost=f'{c1}*n+{c0}'
 out.append(f'theorem growth (n : Nat) : run0 table ({cost}) (family n) = some (family (n+1)) := by\n  have h := h0 n')
 for j in range(1,len(actions)):out.append(f'  have h := join0 h (h{j} n)')
 out.append(f'  rw [endEq] at h\n  change run0 table _ (family n) = _ at h\n  rw [show {cost} = '+ ' + '.join(costs)+' by omega]\n  exact h')
 out.append(f'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=\n  never_of_growth table family {t} (fun n => {cost}) entry (by intro n; omega) growth m hm\n#print axioms never\nend M{i}')
 return '\n'.join(out)
HEADER='''import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace {ns}
open BB6Coverage BB6Coverage.Agent31Pump

theorem commute_rep (d X Y : List Bool) (h : d ++ X = Y ++ d) (n : Nat) :
    d ++ rep X n = rep Y n ++ d := by
  induction n with
  | zero => simp [rep]
  | succ n ih =>
    simp only [rep]
    rw [← List.append_assoc, h, List.append_assoc, ih, List.append_assoc]

theorem commute_context (A B d X Y : List Bool) (h : d ++ X = Y ++ d) (n : Nat) :
    A ++ d ++ rep X n ++ B = A ++ rep Y n ++ d ++ B := by
  simpa only [List.append_assoc] using congrArg (fun x => A ++ x ++ B) (commute_rep d X Y h n)
'''
if __name__=='__main__':
 inp,ns,out=sys.argv[1:];recs=[json.loads(line) for line in Path(inp).read_text().splitlines() if line.strip()];Path(out).write_text(HEADER.format(ns=ns)+'\n\n'.join(map(emit,recs))+'\nend '+ns+'\n')
