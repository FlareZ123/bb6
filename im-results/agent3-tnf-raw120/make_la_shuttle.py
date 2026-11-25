"""Two quadratic-time nested shuttle certificates for the 0LA cylinder."""
from tagmacro import *
from generate_sweeps import parse
from pathlib import Path
import sys

machines = [(3827,'1RB0RE_1RC1LF_0RD1RB_1LD1RE_0LA1LE_---0LB',52,13,9,22),(3830,'1RB1RB_1RC1LF_0RD1RB_1LD1RE_0LA1LE_---0LB',46,11,7,20)]
def emit(opens,folder):
 parts=['import SweepPumping\nnamespace BB6.Agent3LAFinal\nopen BB6Coverage BB6Coverage.Agent31Pump\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\n']
 common='''abbrev O (n : Nat) := rep [true] n
abbrev P (n : Nat) := [false,true,false,true] ++ rep [false,true] n

theorem rep_add (s : List Bool) (a b : Nat) : rep s (a+b) = rep s a ++ rep s b := by
  induction a with
  | zero => simp [rep]
  | succ a ih =>
    rw [show a+1+b=a+b+1 by omega]
    simp only [rep,ih,List.append_assoc]

theorem double (n : Nat) : rep [true,true] n = O (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 2*(n+1)=2*n+2 by omega]; simp only [rep,ih]; rfl

theorem zeroHead (k : Nat) (R : List Bool) :
    run0 table (k+1) ⟨1,[],R⟩ = run0 table (k+1) ⟨1,[false],R⟩ := by rfl
'''
 for i,code,entry,c,d,e in machines:
  assert opens[i]==code
  p=parse(code);parts.extend([f'namespace M{i}',tab(p)])
  starts=[('shuttle',C(1,clean(lit('0')+rep('Y','x')),clean(lit('0101')+rep('01','m')+lit('1')+rep('X','x'))),lambda c:c.q==1 and c.l==clean(lit('01')+rep('Y','x'))),('finish',C(1,clean(lit('0')+rep('Y','x')),clean(lit('0101')+rep('01','m'))),lambda c:c.q==1 and not c.r and c.l[0][0].startswith('0')),('leftback',C(1,clean(lit('0111')+rep('11','m')+lit('0111')+rep('11','n')),()),lambda c:c.q==1 and not c.l)]
  for name,st,stop in starts:parts.append(generate(p,name,st,walk(p,st,stop))[0])
  parts.append(common)
  parts.append(f'''
theorem collect (m k : Nat) (L : List Bool) :
    run0 table (({c}+4*m)*k) ⟨1,false::L,P m++O k⟩ = some ⟨1,false::(O k++L),P m⟩ := by
  induction k generalizing L with
  | zero => simp [rep,run0]
  | succ k ih =>
    have h1 := shuttle.equation m (O k) L
    have h2 := ih (true::L)
    have H := join0 h1 h2
    have hh : O k ++ true::L = O (k+1) ++ L := by
      rw [← List.singleton_append, ← List.append_assoc,rep_snoc]
      rfl
    rw [hh] at H
    rw [Nat.mul_succ,Nat.add_comm (({c}+4*m)*k) ({c}+4*m)]
    simpa only [P,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

def family (n : Nat) : Z0 := ⟨1,[false,true,true,true]++rep [true,true] n++[false,true,true,true]++rep [true,true] n,[]⟩

def cost (n : Nat) : Nat := ({e}+2*n+2*n) + (({c}+4*(n+1))*(2*n+4)) + ({d}+2*(n+1))

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have back := leftback.equation n n
  have hs : [false,true,false,true,false,true]++rep [false,true] n++[true,true,true]++rep [true,true] n++[true] = P (n+1)++O (2*n+4) := by
    rw [double,show 2*n+4=3+2*n+1 by omega]
    unfold O
    rw [rep_add [true] (3+2*n) 1,rep_add [true] 3 (2*n)]
    simp only [P,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil]
  rw [hs] at back
  have gather := collect (n+1) (2*n+4) []
  have hp : 0 < ({c}+4*(n+1))*(2*n+4) := Nat.mul_pos (by omega) (by omega)
  have hz := zeroHead (({c}+4*(n+1))*(2*n+4)-1) (P (n+1)++O (2*n+4))
  rw [show ({c}+4*(n+1))*(2*n+4)-1+1=({c}+4*(n+1))*(2*n+4) by omega] at hz
  simp only [List.append_nil] at gather
  have gather' := hz.trans gather
  have fin := finish.equation (n+1) (O (2*n+4))
  have fin' : run0 table ({d}+2*(n+1)) ⟨1,false::O (2*n+4),P (n+1)⟩ = some (family (n+1)) := by
    rw [family, double]
    rw [show 2*(n+1)=2*n+2 by omega]
    have he : O (2*n+4) = true::true::O (2*n+2) := by rw [show 2*n+4=(2*n+2)+2 by omega]; rfl
    rw [he] at fin ⊢
    rw [double] at fin
    rw [show 2*(n+1)=2*n+2 by omega] at fin
    simp only [P,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] at fin ⊢
    have hm (k : Nat) (R : List Bool) : O k ++ true::R = true::(O k ++ R) := by
      rw [← List.singleton_append, ← List.append_assoc, rep_snoc]
      rfl
    simpa only [hm] using fin
  exact join0 (join0 back gather') fin'

theorem first : run0 table {entry} ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family {entry} cost first (by intro n; unfold cost; omega) growth m hm
#print axioms never
end M{i}
''')
 parts.append('end BB6.Agent3LAFinal')
 (folder/'Raw120LAShuttles.lean').write_text('\n\n'.join(parts)+'\n')
