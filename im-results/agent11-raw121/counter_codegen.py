import counter as c
import quad as q
import quad_codegen as g
import generate_sweeps as one
import sys
from itertools import groupby

def word(w):return g.app(*(v if v=='R' else f'rep {g.bits(s)} {v}' if v else g.bits(s) for s,v in w))
def cfg(c):return f'⟨{c.q}, {word(c.l)}, {word(c.r)}⟩'
def repword(w):
 xs=[]
 for s,v in w:
  if v=='R':xs.append('R')
  elif v:xs.append(f'rep (List.replicate {len(s)} {g.rbit(s[0])}) {v}')
  else:
   for b,it in groupby(s):xs.append(f'List.replicate {len(list(it))} {g.rbit(b)}')
 return g.app(*xs)

def eq(name,w,W,params='(n : Nat) (R : List Bool)'):
 assert c.norm(w)==c.norm(W),(name,w,W)
 return f'''theorem {name} {params} : ({word(w)}) = ({word(W)}) := by
  change ({repword(w)}) = ({repword(W)})
  simp only [repReplicate,replicateAddTail,List.replicate_append_replicate]
  congr 2 <;> (first | omega | congr 1 <;> omega)
'''

header='''import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw121Counter
open BB6Coverage BB6Coverage.Agent31Pump

theorem repReplicate (b : Bool) (k n : Nat) :
    rep (List.replicate k b) n = List.replicate (k*n) b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,ih,List.replicate_append_replicate,show k+k*n=k*(n+1) by rw [Nat.mul_succ,Nat.add_comm]]

theorem replicateAddTail (b : Bool) (a c : Nat) (R : List Bool) :
    List.replicate a b ++ (List.replicate c b ++ R) = List.replicate (a+c) b ++ R := by
  rw [← List.append_assoc,List.replicate_append_replicate]

abbrev U := [true]
abbrev Z := [false]
def atE (k : Nat) (S : List Bool) (n : Nat) (R : List Bool) : Z0 := ⟨4,false::(rep U (n+k)++S),R⟩
def atHead (k : Nat) (S : List Bool) (n : Nat) (R : List Bool) : Z0 := ⟨4,R.headD false::(rep U (n+k)++S),R.tail⟩
def costs (base d s : Nat) : Nat → Nat × Nat
  | 0 => (base,0)
  | n+1 => (d+s*n+(costs base d s n).2+(costs base d s n).1+1,(costs base d s n).2+(costs base d s n).1)

theorem advance_and_prefix (p : PartialMachine) (k : Nat) (S : List Bool) (base d s : Nat)
    (hbase : ∀ R, run0 p base (atE k S 0 R) = some (atHead k S 1 R))
    (hdesc : ∀ n R, run0 p (d+s*n) (atE k S (n+1) R) = some (atE k S 0 (rep Z n++true::R)))
    (hone : ∀ n R, run0 p 1 (atHead k S n (true::R)) = some (atHead k S (n+1) R))
    (n : Nat) :
    (∀ R, run0 p (costs base d s n).1 (atE k S n R) = some (atHead k S (n+1) R)) ∧
    (∀ R, run0 p (costs base d s n).2 (atE k S 0 (rep Z n++R)) = some (atE k S n R)) := by
  induction n with
  | zero => exact ⟨hbase,by intro R; rfl⟩
  | succ n ih =>
    constructor
    · intro R
      have h := join0 (join0 (join0 (hdesc n R) (ih.2 (true::R))) (ih.1 (true::R))) (hone (n+1) R)
      exact h
    · intro R
      have h := join0 (ih.2 (false::R)) (ih.1 (false::R))
      have e : rep Z n ++ false::R = rep Z (n+1) ++ R := by
        change rep Z n ++ (Z++R) = (Z++rep Z n)++R
        rw [← List.append_assoc,rep_snoc]
      rw [e] at h
      exact h
'''

def generate(i,p,local=False):
 k,suf,base,d,s,entry,off=c.SPECS[i]
 st,tg,ans=c.desc(p,k,suf);hist,last=ans;ss=g.segs(hist);out=[f'namespace M{i}',g.table(p)];costs=[]
 for j,a in enumerate(ss):
  typ,C,D,K=a[:4];name=f'descStep{j}'
  if typ=='step':
   out.append(f'theorem {name} (n : Nat) (R : List Bool) : run0 table {K} {cfg(C)} = some {cfg(D)} := by rfl');costs.append(str(K));continue
  _,_,_,K,sd,I,O,cut,v=a;assert v=='n'
  if sd=='L':
   lp,rp=q.pre(C.l),q.pre(C.r)[:cut];L,T=q.rest(C.l)[1:],q.clean(q.lit(q.pre(C.r)[cut:])+q.rest(C.r));src=g.cf(C.q,g.app(g.bits(lp),g.bits(I),'L'),g.app(g.bits(rp),'T'));dst=g.cf(C.q,g.app(g.bits(lp),'L'),g.app(g.bits(rp),g.bits(O),'T'))
  else:
   lp,rp=q.pre(C.l)[:cut],q.pre(C.r);L,T=q.clean(q.lit(q.pre(C.l)[cut:])+q.rest(C.l)),q.rest(C.r)[1:];src=g.cf(C.q,g.app(g.bits(lp),'L'),g.app(g.bits(rp),g.bits(I),'T'));dst=g.cf(C.q,g.app(g.bits(lp),g.bits(O),'L'),g.app(g.bits(rp),'T'))
  out.append(f'theorem descLocal{j} (L T : List Bool) : run0 table {K} {src} = some {dst} := by rfl')
  out.append(f'theorem {name} (n : Nat) (R : List Bool) : run0 table ({K}*n) {cfg(C)} = some {cfg(D)} := by\n  simpa only [{g.simp}] using sweep{sd} table {C.q} {g.bits(lp)} {g.bits(rp)} {g.bits(I)} {g.bits(O)} {K} descLocal{j} n ({word(L)}) ({word(T)})');costs.append(f'{K}*n')
 es=[]
 for sd in ('l','r'):
  w,W=getattr(last,sd),getattr(tg,sd)
  if w!=W:
   name=f'descEq{sd.upper()}';es.append(name);out.append(eq(name,w,W))
 out.append(f'theorem descRaw (n : Nat) (R : List Bool) : run0 table ({d}+{s}*n) {cfg(st)} = some {cfg(tg)} := by\n  have H := descStep0 n R\n'+'\n'.join(f'  have H := join0 H (descStep{j} n R)' for j in range(1,len(ss)))+f"\n  rw [show {'+'.join(costs)}={d}+{s}*n by omega] at H\n"+'\n'.join(f'  rw [{name} n R] at H' for name in es)+'\n  exact H')
 std=q.clean(q.lit('0'+'1'*(k+1))+q.rep('1','n')+q.lit(suf));name='descStart';out.append(eq(name,st.l,std,'(n : Nat)'))
 out.append(f'''abbrev S : List Bool := {g.bits(suf)}
theorem desc (n : Nat) (R : List Bool) : run0 table ({d}+{s}*n) (atE {k} S (n+1) R) = some (atE {k} S 0 (rep Z n++true::R)) := by
  have H := descRaw n R
  rw [descStart n] at H
  simpa only [atE,S,rep,{g.simp}] using H

theorem base (R : List Bool) : run0 table {base} (atE {k} S 0 R) = some (atHead {k} S 1 R) := by
  cases R with
  | nil => rfl
  | cons b R => cases b <;> rfl

theorem one (n : Nat) (R : List Bool) : run0 table 1 (atHead {k} S n (true::R)) = some (atHead {k} S (n+1) R) := by rfl

def family (n : Nat) := atE {k} S (n+{off}) []
def cost (n : Nat) := (costs {base} {d} {s} (n+{off})).1

theorem entry : run0 table {entry} ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have H := (advance_and_prefix table {k} S {base} {d} {s} base desc one (n+{off})).1 []
  rw [show n+{off}+1=n+1+{off} by omega] at H
  exact H

theorem positive (n : Nat) : 0 < cost n := by
  unfold cost
  cases h : n+{off} <;> simp only [costs] <;> omega
''')
 if not local:out.append(f'''theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family {entry} cost entry positive growth m hm
#print axioms never''')
 out.append('#print axioms growth\nend M'+str(i));return '\n\n'.join(out)
