"""Construct checked counter/sweep modules for RF leaves (discovery only)."""
from tagmacro import *
from generate_sweeps import parse
from pathlib import Path
CASES={1658:(2,'100',44,2,2,4),1676:(5,'00',37,2,2,6),1677:(5,'00',35,2,1,6)}
TABLES={1658:"1RB0LA_1RC---_0RD0RA_1LD1RE_1RF1LE_1LC0LF",1676:"1RB0LA_1RC---_0RD0RA_1LD1RE_1RF1LE_1RA0LF",1677:"1RB---_1RC0LA_0RD0RB_1LD1RE_1RF1LE_1RA0LF",1678:"1RB---_1RC0RC_0RD0RB_1LD1RE_1RF1LE_1RA0LF"}
HEADER='''import PhaseClosure
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
open BB6Coverage BB6Coverage.Agent31Pump
'''
COMMON='''theorem rotateOne (a : Nat) (R : List Bool) : rep [true,true,true,true] a ++ true::R = true::(rep [true,true,true,true] a ++ R) := by
  induction a with
  | zero => rfl
  | succ a ih => simp only [rep,List.append_assoc,List.cons_append,List.nil_append,ih]

theorem zeros4 (a : Nat) : rep [false,false,false,false] a = rep [false,false] (2*a) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [show 2*(a+1)=2*a+1+1 by omega]
    simp only [rep,ih,List.cons_append,List.nil_append]
'''
def finish(i,entry):
 return f'''noncomputable def family (n : Nat) : Z0 := (phaseOrbit table Good progress initial n).val
noncomputable def cost (n : Nat) : Nat := phaseTime table Good progress (phaseOrbit table Good progress initial n)
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := phaseOrbit_step table Good progress initial n
theorem positive (n : Nat) : 0 < cost n := phaseTime_pos table Good progress (phaseOrbit table Good progress initial n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family {entry} cost entry positive growth m hm
#print axioms never
end BB6.Agent3Raw120OneRF.M{i}'''
def make(i,t):
 q,pre,entry,b0,c0,reset=CASES[i];p=parse(t);out=[f'namespace BB6.Agent3Raw120OneRF.M{i}',f'-- {t}',tab(p),COMMON]
 res={}
 for name,parts in [('Grow',lit(pre)+rep('1111','a')+lit('000')+rep('00','b')+rep('X','tail')),('EndMany',lit(pre)+rep('1111','a')+lit('011')+rep('1','c')),('EndOne',lit(pre)+rep('1111','a')+lit('01'))]:
  st=C(q,(),clean(parts));rr=walk(p,st,lambda c:c.q==q and not c.l);code,cost=generate(p,name,st,rr);out.append(code);res[name]=(cost,rr[1])
 prelean=bits(pre)
 out.append(f'''def cfg (a b c : Nat) : Z0 := ⟨{q},[],{prelean}++rep [true,true,true,true] a++[false]++rep [false,false] b++[true]++rep [true] c⟩

theorem grow (a b c : Nat) : run0 table ({res['Grow'][0]}) (cfg a (b+1) c) = some (cfg (a+1) b c) := by
  have H := Grow.equation a b (true::rep [true] c)
  simp only [cfg,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] at H ⊢
  rw [rotateOne] at H
  exact H

theorem endMany (a c : Nat) : run0 table ({res['EndMany'][0]}) (cfg a 0 (c+1)) = some (cfg 0 (2*a+1) c) := by
  have H := EndMany.equation a c
  rw [zeros4] at H
  simp only [cfg,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] at H ⊢
  exact H

theorem endOne (a : Nat) : run0 table ({res['EndOne'][0]}) (cfg a 0 0) = some (cfg 0 (2*a+1) {reset-1}) := by
  have H := EndOne.equation a
  rw [zeros4] at H
  simp only [cfg,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] at H ⊢
  exact H

inductive Good : Z0 → Prop where
  | intro (a b c : Nat) : Good (cfg a b c)

theorem progress (z : Z0) (hz : Good z) : ∃ t d, 0 < t ∧ run0 table t z = some d ∧ Good d := by
  cases hz with
  | intro a b c =>
    cases b with
    | zero =>
      cases c with
      | zero => exact ⟨_,_,by omega,endOne a,Good.intro 0 (2*a+1) {reset-1}⟩
      | succ c => exact ⟨_,_,by omega,endMany a c,Good.intro 0 (2*a+1) c⟩
    | succ b => exact ⟨_,_,by omega,grow a b c,Good.intro (a+1) b c⟩

def initial : {{z // Good z}} := ⟨cfg 0 {b0} {c0}, Good.intro 0 {b0} {c0}⟩
theorem entry : run0 table {entry} ⟨0,[],[]⟩ = some initial.val := by rfl
''')
 out.append(finish(i,entry))
 return '\n\n'.join(out)

def make_d(t):
 p=parse(t);out=['namespace BB6.Agent3Raw120OneRF.M1678',tab(p)]
 for name,parts in [('Grow',lit('0000')+rep('0000','a')+lit('111000')+rep('00','b')+lit('111000')+rep('X','tail')),('Reset',lit('0000')+rep('0000','a')+lit('1110111000')+rep('X','tail'))]:
  st=C(3,clean(parts),());rr=walk(p,st,lambda c:c.q==3 and not c.r and prefix(c.l).startswith('0000'));code,cost=generate(p,name,st,rr);out.append(code)
 out.append('''theorem zeros4 (a : Nat) : rep [false,false,false,false] a = rep [false,false] (2*a) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [show 2*(a+1)=2*a+1+1 by omega]
    simp only [rep,ih,List.cons_append,List.nil_append]

def cfg (a b c : Nat) : Z0 := ⟨3,[false,false,false,false]++rep [false,false,false,false] a++[true,true,true,false]++rep [false,false] b++[true,true,true,false,false,false]++rep [true] c,[]⟩

theorem grow (a b c : Nat) : run0 table (22+8*a) (cfg a (b+1) c) = some (cfg (a+1) b c) := by
  simpa only [cfg,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Grow.equation a b (rep [true] c)

theorem reset (a c : Nat) : run0 table (67+8*a) (cfg a 0 c) = some (cfg 0 (2*a+1) (c+3)) := by
  have H := Reset.equation a (rep [true] c)
  simp only [cfg,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil,zeros4] at H ⊢
  exact H

inductive Good : Z0 → Prop where
  | intro (a b c : Nat) : Good (cfg a b c)
theorem progress (z : Z0) (hz : Good z) : ∃ t d, 0<t ∧ run0 table t z = some d ∧ Good d := by
  cases hz with
  | intro a b c =>
    cases b with
    | zero => exact ⟨_,_,by omega,reset a c,Good.intro 0 (2*a+1) (c+3)⟩
    | succ b => exact ⟨_,_,by omega,grow a b c,Good.intro (a+1) b c⟩

def initial : {z // Good z} := ⟨cfg 0 1 3,Good.intro 0 1 3⟩
theorem entry : run0 table 101 ⟨0,[],[]⟩ = some initial.val := by rfl
''')
 out.append(finish(1678,101))
 return '\n\n'.join(out)

def emit(opens,folder):
 for i,t in TABLES.items(): assert opens[i]==t,(i,opens[i],t)
 (folder/'Raw120OneRFCounter.lean').write_text(HEADER+'\n\n'.join([make(i,TABLES[i]) for i in CASES]+[make_d(TABLES[1678])])+'\n')
