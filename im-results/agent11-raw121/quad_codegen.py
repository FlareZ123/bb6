"""Untrusted symbolic producer; each generated universal equality is checked in Lean."""
import quad as q
import generate_sweeps as g
from itertools import groupby

def bits(s):return '['+','.join('true' if b=='1' else 'false' for b in s)+']'
def app(*xs):
 xs=[x for x in xs if x!='[]'];out='[]'
 for x in reversed(xs):out='('+x+')' if out=='[]' else '('+x+') ++ ('+out+')'
 return out
def word(w):return app(*(f'rep {bits(s)} {v}' if v else bits(s) for s,v in w))
def cfg(c):return f'⟨{c.q}, {word(c.l)}, {word(c.r)}⟩'
def table(p):
 lines=['def table : PartialMachine := fun s =>','  match s.1.val,s.2 with']
 for i,a in enumerate(p):
  if a=='---':continue
  lines.append(f"  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(a[0]=='1').lower()},{str(a[1]=='R').lower()},{ord(a[2])-65}⟩)")
 lines.append('  | _,_ => none');return '\n'.join(lines)
def cf(q,l,r):return f'⟨{q}, {l}, {r}⟩'
def coeff(a):return '+'.join([str(a[0])]+[f'{c}*{v}' for c,v in zip(a[1:],['n','j']) if c])
def rbit(b):return 'true' if b=='1' else 'false'
def repword(w):
 xs=[]
 for s,v in w:
  if v:xs.append(f'rep (List.replicate {len(s)} {rbit(s[0])}) {v}')
  else:
   for b,it in groupby(s):xs.append(f'List.replicate {len(list(it))} {rbit(b)}')
 return app(*xs)
def segs(hist):
 out=[];i=0
 while i<len(hist):
  if hist[i][0]=='loop':out.append(hist[i]);i+=1;continue
  j=i+1
  while j<len(hist) and hist[j][0]=='step':j+=1
  out.append(('step',hist[i][1],hist[j-1][2],j-i));i=j
 return out
simp='List.append_assoc,List.nil_append,List.append_nil,List.cons_append'

def generate_phase(name,st,tg,ans):
 hist,last=ans;ss=segs(hist);costs=[];out=[];vs=sorted({v for c in (st,tg) for w in (c.l,c.r) for s,v in w if v},reverse=True)
 params=' '.join(vs);bindings=f'({params} : Nat)' if params else ''
 for i,a in enumerate(ss):
  typ,c,d,k=a[:4];lemma=f'{name}Step{i}'
  if typ=='step':
   out.append(f'theorem {lemma} {bindings} : run0 table {k} {cfg(c)} = some {cfg(d)} := by rfl')
   costs.append(str(k));continue
  _,_,_,k,sd,I,O,cut,v=a
  if sd=='L':
   lp,rp=q.pre(c.l),q.pre(c.r)[:cut]
   L,R=q.rest(c.l)[1:],q.clean(q.lit(q.pre(c.r)[cut:])+q.rest(c.r))
   src=cf(c.q,app(bits(lp),bits(I),'L'),app(bits(rp),'R'));dst=cf(c.q,app(bits(lp),'L'),app(bits(rp),bits(O),'R'))
  else:
   lp,rp=q.pre(c.l)[:cut],q.pre(c.r)
   L,R=q.clean(q.lit(q.pre(c.l)[cut:])+q.rest(c.l)),q.rest(c.r)[1:]
   src=cf(c.q,app(bits(lp),'L'),app(bits(rp),bits(I),'R'));dst=cf(c.q,app(bits(lp),bits(O),'L'),app(bits(rp),'R'))
  out.append(f'theorem {name}Local{i} (L R : List Bool) : run0 table {k} {src} = some {dst} := by rfl')
  out.append(f'theorem {lemma} {bindings} : run0 table ({k}*{v}) {cfg(c)} = some {cfg(d)} := by\n  simpa only [{simp}] using sweep{sd} table {c.q} {bits(lp)} {bits(rp)} {bits(I)} {bits(O)} {k} {name}Local{i} {v} ({word(L)}) ({word(R)})')
  costs.append(f'{k}*{v}')
 a=sum(x[3] for x in ss if x[0]=='step');b=sum(x[3] for x in ss if x[0]=='loop' and x[-1]=='n');c=sum(x[3] for x in ss if x[0]=='loop' and x[-1]=='j');cost=coeff((a,b,c))
 eqs=[]
 for sd in ('l','r'):
  w,W=getattr(last,sd),getattr(tg,sd)
  if w==W:continue
  assert q.norm(w)==q.norm(W)
  en=f'{name}Eq{sd.upper()}';eqs.append(en)
  out.append(f'theorem {en} {bindings} : ({word(w)}) = ({word(W)}) := by\n  change ({repword(w)}) = ({repword(W)})\n  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]\n  congr 2 <;> (first | omega | congr 1 <;> omega)')
 out.append(f'theorem {name}Raw {bindings} : run0 table ({cost}) {cfg(st)} = some {cfg(tg)} := by')
 out.append(f'  have H := {name}Step0 {params}')
 for i in range(1,len(ss)):out.append(f'  have H := join0 H ({name}Step{i} {params})')
 out.append(f"  rw [show {'+'.join(costs)} = {cost} by omega] at H")
 for en in eqs:out.append(f'  rw [{en} {params}] at H')
 out.append('  exact H')
 return '\n\n'.join(out),(a,b,c)

header='''import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw121Quadratic
open BB6Coverage BB6Coverage.Agent31Pump

theorem repReplicate (b : Bool) (k n : Nat) :
    rep (List.replicate k b) n = List.replicate (k*n) b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,ih,List.replicate_append_replicate,show k+k*n=k*(n+1) by rw [Nat.mul_succ,Nat.add_comm]]

theorem replicateAddTail (b : Bool) (a c : Nat) (R : List Bool) :
    List.replicate a b ++ (List.replicate c b ++ R) = List.replicate (a+c) b ++ R := by
  rw [← List.append_assoc,List.replicate_append_replicate]

abbrev P := [true,true]
abbrev U := [true]
def family (n : Nat) : Z0 := ⟨4,false::rep P (n+2),[]⟩
def middle (n j : Nat) : Z0 := ⟨4,false::(rep P (n+1)++false::rep U (j+1)),rep U (j+1)⟩
def innerCost (a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => a+4*n+innerCost a n

theorem innerAll (p : PartialMachine) (a : Nat)
    (one : ∀ n j, run0 p (a+4*n) (middle (n+1) j) = some (middle n (j+1)))
    (n j : Nat) : run0 p (innerCost a n) (middle n j) = some (middle 0 (j+n)) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    have H := join0 (one n j) (ih (j+1))
    simpa only [innerCost,show j+1+n=j+(n+1) by omega] using H

def cost (a b c n : Nat) := a+4*n+innerCost b n+(c+n)
theorem growthAll (p : PartialMachine) (a b c : Nat)
    (first : ∀ n, run0 p (a+4*n) (family n) = some (middle n 0))
    (one : ∀ n j, run0 p (b+4*n) (middle (n+1) j) = some (middle n (j+1)))
    (last : ∀ j, run0 p (c+j) (middle 0 j) = some (family (j+1)))
    (n : Nat) : run0 p (cost a b c n) (family n) = some (family (n+1)) := by
  have H := join0 (first n) (innerAll p b one n 0)
  rw [Nat.zero_add] at H
  exact join0 H (last n)
'''
def generate(i,p,local=False):
 out=[f'namespace M{i}',table(p)]
 co=[]
 for name,st,tg,ans in q.phases(p):
  assert ans,(i,name);s,c=generate_phase(name,st,tg,ans);out.append(s);co.append(c)
 a,b,c=co[0][0],co[1][0],co[2][0]
 assert co==[(a,4,0),(b,4,0),(c,0,1)],co
 out.append(f'''theorem first (n : Nat) : run0 table ({a}+4*n) (family n) = some (middle n 0) := by
  simpa only [family,middle,rep,{simp}] using firstRaw n

theorem inner (n j : Nat) : run0 table ({b}+4*n) (middle (n+1) j) = some (middle n (j+1)) := by
  simpa only [middle,rep,{simp}] using innerRaw n j

theorem finish (j : Nat) : run0 table ({c}+j) (middle 0 j) = some (family (j+1)) := by
  simpa only [family,middle,rep,{simp},Nat.one_mul] using finishRaw j

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost {a} {b} {c} n) (family n) = some (family (n+1)) :=
  growthAll table {a} {b} {c} first inner finish n
''')
 if not local:out.append(f'''theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (cost {a} {b} {c}) entry (by intro n; unfold cost; omega) growth m hm
#print axioms never''')
 out.append('#print axioms growth\nend M'+str(i))
 return '\n\n'.join(out)
