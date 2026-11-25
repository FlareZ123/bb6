"""Construct the RF run-list grammar and recursive shuttle certificates."""
from tagmacro import *
from generate_sweeps import parse
from pathlib import Path
TABLES={2120:"1RB0LE_1RC1LA_0RD0LE_1LD1RE_1RF1LE_---0RB",2118:"1RB0LB_1RC1LA_0RD1RE_1LD1RE_1RF1LE_---0RB"}
HEADER='''import PhaseClosure
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
open BB6Coverage BB6Coverage.Agent31Pump
'''
def stack(t):
 p=parse(t);Y=rep('Y','tail');X=rep('X','tail');L=lit;R=rep;cl=clean
 out=['namespace BB6.Agent3Raw120OneRF.M2120',tab(p)]
 for name,st,stop in [
  ('End',C(4,cl(L('0')+R('1','k')+Y),L('10')),lambda c:c.q==4 and c.l==Y),
  ('Big',C(4,cl(L('0')+R('1','k')+Y),cl(L('10011')+X)),lambda c:c.q==4 and c.l==Y),
  ('PairBig',C(4,cl(L('0')+R('1','k')+Y),cl(L('1001011')+X)),lambda c:c.q==4 and c.l==Y),
  ('PairOne',C(4,cl(L('0')+R('1','k')+Y),L('100101')),lambda c:c.q==4 and c.l==Y),
  ('PairScan',C(4,cl(L('0')+R('1','k')+Y),cl(L('1001010')+X)),lambda c:c.q==4 and c.l!=Y and prefix(c.r).startswith('10')),
  ('Pop',C(4,cl(L('0')+R('1','k')+Y),cl(L('11')+X)),lambda c:c.q==4 and c.l==Y),
  ('Scan',C(4,cl(L('0')+Y),cl(L('10')+R('1','m')+X)),lambda c:c.q==4 and c.r==cl(L('10')+X)),
 ]:
  rr=walk(p,st,stop);code,cost=generate(p,name,st,rr);out.append(code)
 out.append('''abbrev O (n : Nat) := rep [true] n

theorem addO (a b : Nat) : O a ++ O b = O (a+b) := by
  induction a with
  | zero => simp [rep]
  | succ a ih =>
    rw [show a+1+b=a+b+1 by omega]
    simp only [rep,List.cons_append,List.nil_append,ih]

theorem moveO (a : Nat) (R : List Bool) : O a ++ true::R = true::(O a++R) := by
  induction a with
  | zero => rfl
  | succ a ih => simp only [rep,List.cons_append,List.nil_append,ih]

theorem scan (k m : Nat) (L R : List Bool) :
    run0 table (5*m) ⟨4,false::(O k++L),true::false::(O m++R)⟩ = some ⟨4,false::(O (k+m)++L),true::false::R⟩ := by
  have H := Scan.equation m R (O k++L)
  simp only [List.append_assoc] at H
  rw [← List.append_assoc (O m) (O k) L,addO,show m+k=k+m by omega] at H
  simpa only [Nat.zero_add,List.append_assoc,List.cons_append,List.nil_append] using H

theorem pop (k : Nat) (L R : List Bool) :
    run0 table (7+k) ⟨4,false::(O k++L),true::true::R⟩ = some ⟨4,L,O (k+1)++false::true::R⟩ := by
  simpa only [rep,List.cons_append,List.nil_append,List.append_assoc,List.append_nil,Nat.one_mul] using Pop.equation k R L

inductive Tail where
  | nil
  | two
  | pairOne
  | b (n : Nat) (t : Tail)
  | c (n : Nat) (t : Tail)
  deriving Repr

def word : Tail → List Bool
  | .nil => []
  | .two => [false,true,true]
  | .pairOne => [false,true,false,true]
  | .b n t => false::true::false::(O (n+2)++word t)
  | .c n t => false::true::false::true::false::(O (n+1)++word t)

def next : Tail → Tail
  | .nil => .two
  | .two => .pairOne
  | .pairOne => .b 0 .two
  | .b n t => .c n t
  | .c n t => .b (n+1) (next t)

theorem process (t : Tail) (k m : Nat) (L : List Bool) :
    ∃ time, 0 < time ∧ run0 table time ⟨4,false::(O k++L),true::false::(O m++word t)⟩ =
      some ⟨4,L,O (k+m+2)++word (next t)⟩ := by
  induction t generalizing k m L with
  | nil =>
    have h1 := scan k m L []
    have h2 := End.equation (k+m) L
    have H := join0 h1 h2
    exact ⟨5*m+(17+1*(k+m)),by omega,by simpa only [word,next,rep,List.cons_append,List.nil_append,List.append_assoc,List.append_nil,Nat.one_mul] using H⟩
  | two =>
    have h1 := scan k m L (word .two)
    have h2 := Big.equation (k+m) [] L
    have H := join0 h1 h2
    exact ⟨5*m+(23+1*(k+m)),by omega,by simpa only [word,next,rep,List.cons_append,List.nil_append,List.append_assoc,List.append_nil,Nat.one_mul] using H⟩
  | pairOne =>
    have h1 := scan k m L (word .pairOne)
    have h2 := PairOne.equation (k+m) L
    have H := join0 h1 h2
    exact ⟨5*m+(39+1*(k+m)),by omega,by simpa only [word,next,rep,List.cons_append,List.nil_append,List.append_assoc,List.append_nil,Nat.one_mul] using H⟩
  | b n t ih =>
    have h1 := scan k m L (word (.b n t))
    have h2 := PairBig.equation (k+m) (O n++word t) L
    have H := join0 h1 h2
    exact ⟨5*m+(29+1*(k+m)),by omega,by simpa only [word,next,rep,List.cons_append,List.nil_append,List.append_assoc,List.append_nil,Nat.one_mul] using H⟩
  | c n t ih =>
    have h1 := scan k m L (word (.c n t))
    have h2 := PairScan.equation (k+m) (O (n+1)++word t) L
    obtain ⟨time,ht,h3⟩ := ih 1 (n+1) (false::true::false::true::(O (k+m)++L))
    rw [show 1+(n+1)+2=n+4 by omega] at h3
    have h4 := pop 1 (false::true::(O (k+m)++L)) (O (n+2)++word (next t))
    have h5 := pop (k+m+1) L (false::(O (n+3)++word (next t)))
    have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
    exact ⟨5*m+5+time+(7+1)+(7+(k+m+1)),by omega,by simpa only [word,next,rep,List.cons_append,List.nil_append,List.append_assoc,List.append_nil,Nat.one_mul,show n+1+2=n+3 by omega] using H⟩

theorem splitRoot (R : List Bool) : run0 table 7 ⟨4,[],true::true::R⟩ = some ⟨4,[],true::false::true::R⟩ := by rfl

theorem consumeRoot (R : List Bool) : run0 table 5 ⟨4,[],true::false::true::R⟩ = some ⟨4,[false,true],true::false::R⟩ := by rfl

def cfg (n : Nat) (t : Tail) : Z0 := ⟨4,[],O (n+4)++word t⟩

theorem advance (n : Nat) (t : Tail) : ∃ time, 0 < time ∧ run0 table time (cfg n t) = some (cfg (n+1) (next t)) := by
  have h1 := splitRoot (O (n+2)++word t)
  have h2 := consumeRoot (O (n+2)++word t)
  obtain ⟨time,ht,h3⟩ := process t 1 (n+2) []
  have H := join0 (join0 h1 h2) h3
  exact ⟨7+5+time,by omega,by simpa only [cfg,rep,List.cons_append,List.nil_append,List.append_assoc,List.append_nil,show 1+(n+2)+2=n+1+4 by omega] using H⟩

inductive Good : Z0 → Prop where
  | intro (n : Nat) (t : Tail) : Good (cfg n t)

theorem progress (z : Z0) (hz : Good z) : ∃ time d, 0<time ∧ run0 table time z = some d ∧ Good d := by
  cases hz with
  | intro n t =>
    obtain ⟨time,ht,hr⟩ := advance n t
    exact ⟨time,_,ht,hr,Good.intro (n+1) (next t)⟩

def initial : {z // Good z} := ⟨cfg 0 .nil,Good.intro 0 .nil⟩
theorem entry : run0 table 9 ⟨0,[],[]⟩ = some initial.val := by rfl
noncomputable def family (n : Nat) : Z0 := (phaseOrbit table Good progress initial n).val
noncomputable def cost (n : Nat) : Nat := phaseTime table Good progress (phaseOrbit table Good progress initial n)
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := phaseOrbit_step table Good progress initial n
theorem positive (n : Nat) : 0<cost n := phaseTime_pos table Good progress (phaseOrbit table Good progress initial n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 9 cost entry positive growth m hm
#print axioms never
end BB6.Agent3Raw120OneRF.M2120
''')
 return '\n\n'.join(out)

def nested(t):
 p=parse(t);r=clean(lit('010')+rep('1010','n')+lit('11'));Y=rep('Y','tail')
 out=['namespace BB6.Agent3Raw120OneRF.M2118',tab(p)]
 for name,st,stop in [('CorePrefix',C(1,clean(lit('1101')+Y),r),lambda c:c.q==1 and c.l and c.l[0][1]=='n'),('PopQ',C(1,clean(lit('1011')+Y),r),lambda c:c.q==1 and c.l==Y),('GlobalPrefix',C(1,(),r),lambda c:c.q==1 and c.l and c.l[0][1]=='n')]:
  rr=walk(p,st,stop);code,cost=generate(p,name,st,rr);out.append(code)
 out.append('''def P : List Bool := [true,true,false,true]
def Q : List Bool := [true,false,true,true]
def R (n : Nat) : List Bool := [false,true,false]++rep [true,false,true,false] n++[true,true]
def cfg (L : List Bool) (n : Nat) : Z0 := ⟨1,L,R n⟩

theorem prefixCore (n : Nat) (L : List Bool) : run0 table (20+4*n) (cfg (P++L) n) = some (cfg (rep P n++Q++L) 0) := by
  simpa only [cfg,P,Q,R,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using CorePrefix.equation n L

theorem pop (n : Nat) (L : List Bool) : run0 table 6 (cfg (Q++L) n) = some (cfg L (n+1)) := by
  simpa only [cfg,P,Q,R,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using PopQ.equation n L

theorem sweepCore (bound : Nat) (h : ∀ j < bound, ∀ L, ∃ t, run0 table t (cfg (P++L) j) = some (cfg L (j+1))) (r j : Nat) (L : List Bool) (hj : j+r≤bound) : ∃ t, run0 table t (cfg (rep P r++L) j) = some (cfg L (j+r)) := by
  induction r generalizing j L with
  | zero => exact ⟨0,by simp [rep,run0]⟩
  | succ r ih =>
    obtain ⟨t,ht⟩ := h j (by omega) (rep P r++L)
    obtain ⟨u,hu⟩ := ih (j+1) L (by omega)
    refine ⟨t+u,?_⟩
    rw [show j+(r+1)=j+1+r by omega]
    simpa only [rep,List.append_assoc] using join0 ht hu

theorem core (n : Nat) (L : List Bool) : ∃ t, run0 table t (cfg (P++L) n) = some (cfg L (n+1)) := by
  induction n using Nat.strongRecOn generalizing L with
  | ind n ih =>
    obtain ⟨t,ht⟩ := sweepCore n ih n 0 (Q++L) (by omega)
    simp only [Nat.zero_add] at ht
    have h := join0 (prefixCore n L) (by simpa only [List.append_assoc] using ht)
    exact ⟨_,join0 h (pop n L)⟩

theorem globalPrefix (n : Nat) : run0 table (31+14*n) (cfg [] n) = some (cfg (rep P n++Q) 0) := by
  simpa only [cfg,P,Q,R,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using GlobalPrefix.equation n

theorem advance (n : Nat) : ∃ t, 0<t ∧ run0 table t (cfg [] n) = some (cfg [] (n+1)) := by
  obtain ⟨t,ht⟩ := sweepCore n (fun j _ L => core j L) n 0 Q (by omega)
  simp only [Nat.zero_add] at ht
  refine ⟨31+14*n+t+6,by omega,?_⟩
  exact join0 (join0 (globalPrefix n) ht) (by simpa only [List.append_nil] using pop n [])

def family (n : Nat) : Z0 := cfg [] (n+2)
noncomputable def cost (n : Nat) : Nat := Classical.choose (advance (n+2))
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h := (Classical.choose_spec (advance (n+2))).2
  simpa only [family,cost,show n+2+1=n+1+2 by omega] using h
theorem positive (n : Nat) : 0<cost n := (Classical.choose_spec (advance (n+2))).1
theorem entry : run0 table 127 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 127 cost entry positive growth m hm
#print axioms never
end BB6.Agent3Raw120OneRF.M2118
''')
 return '\n\n'.join(out)

def emit(opens,folder):
 for i,t in TABLES.items(): assert opens[i]==t,(i,opens[i],t)
 (folder/'Raw120OneRFRecursive.lean').write_text(HEADER+stack(TABLES[2120])+'\n\n'+nested(TABLES[2118])+'\n')
