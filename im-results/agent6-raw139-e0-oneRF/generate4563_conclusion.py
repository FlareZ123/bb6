"""Emit the finite addition-chain endpoints and final source-level theorem.
Call after generate4563.py. All generated lemmas are kernel checked.
"""
from pathlib import Path
import sys
from generate4563 import P, M0, M1, U, Q, K, wordlean

out=Path(sys.argv[1]);assert (out/'RF4563Base.lean').is_file()

def header(imports):
 return ''.join('import '+m+'\n' for m in imports)+'''set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace BB6.Agent6RF4563
open BB6Coverage BB6.Agent6NatTape BB6.Agent6WordNat BB6.Agent6SymWord BB6.Agent6RuleCompose BB6.Agent6SymTrace

'''
def write(name,text):
 (out/(name+'.lean')).write_text(text+'\nend BB6.Agent6RF4563\n')

reps=header(['RF4563Base'])
for name,w in [('A',P+M0),('U',U),('B',M1+M0*6+Q),('K',K)]:
 reps+=f'def {name} : Word := {wordlean(w)}\n'
proofs=[];done=set()
def rpt(n):
 if n in done:return
 if n<=1:
  proofs.append(f'theorem repK{n} : K.rep {n} = {wordlean(K*n)} := by decide +kernel\n');done.add(n);return
 a=n//2;b=n-a;rpt(a);rpt(b)
 tail=f',repK{b}' if a!=b else ''
 proofs.append(f'theorem repK{n} : K.rep {n} = {wordlean(K*n)} := by\n  rw [show {n}={a}+{b} by decide,Word.rep_add,repK{a}{tail}]\n  decide +kernel\n');done.add(n)
rpt(553);rpt(619);write('RF4563Reps',reps+''.join(proofs))
shift=header(['RF4563Reps'])+f'''def shifted : State := ⟨[.lit A,.lit U,.rep U false,.lit B,.lit {wordlean(K*553)},.rep K true],[]⟩

#print axioms repK619
theorem shifted_eq (x y : Nat) : periodEnd.eval x y = periodStart.eval (x+1) (y+553) := by
  rw [State.same_sound widths periodEnd shifted (by decide +kernel) x y]
  simp only [shifted,periodStart,State.eval,BB6.Agent6SymWord.eval,env, Bool.false_eq_true,ite_false,ite_true]
  rw [show x+1=1+x by omega,show y+553=553+y by omega,Word.rep_add,Word.rep_add,Word.cat_apply,Word.cat_apply]
  change (⟨4,A.apply (U.apply ((U.rep x).apply (B.apply (({wordlean(K*553)} : Word).apply ((K.rep y).apply 0))))),0⟩ : N1) = _
  rw [←repK553]
  rfl

#print axioms shifted_eq
'''
write('RF4563Shift',shift)
write('RF4563Initial',header(['RF4563Shift'])+'''def family (k : Nat) : N1 := periodStart.eval k (619+553*k)
def periodCost : Cost := ⟨24481769,1294020,79632⟩
def seedCost : Cost := ⟨28792190,0,0⟩
def cost (k : Nat) := periodCost.eval k (619+553*k)

theorem initial (h : ∀ x y : Nat, runN p (seedCost.eval x y) (seedStart.eval x y) = some (seedEnd.eval x y)) :
    runN p 28792194 ⟨0,0,0⟩ = some (family 0) := by
  have h0 : runN p 4 ⟨0,0,0⟩ = some (seedStart.eval 0 0) := by decide +kernel
  have h1 := h 0 0
  have hf : family 0 = ⟨4,A.apply ((U.rep 0).apply (B.apply ((K.rep 619).apply 0))),0⟩ := rfl
  have he : seedEnd.eval 0 0 = family 0 := by
    rw [hf,repK619]
    decide +kernel
  rw [he] at h1
  have hh : runN p (4+seedCost.eval 0 0) ⟨0,0,0⟩ = some (family 0) := runN_join h0 h1
  have hc : 4+seedCost.eval 0 0 = 28792194 := by decide +kernel
  rwa [hc] at hh

#print axioms initial
''')
write('RF4563Conclusion',header(['RF4563Initial'])+'''theorem growth (h : ∀ x y : Nat, runN p (periodCost.eval x y) (periodStart.eval x y) = some (periodEnd.eval x y)) (k : Nat) :
    runN p (cost k) (family k) = some (family (k+1)) := by
  have H := h k (619+553*k)
  rw [shifted_eq] at H
  unfold family cost
  rw [show 619+553*(k+1)=619+553*k+553 by omega]
  exact H

theorem never_of_traces
    (s : ∀ x y : Nat, runN p (seedCost.eval x y) (seedStart.eval x y) = some (seedEnd.eval x y))
    (h : ∀ x y : Nat, runN p (periodCost.eval x y) (periodStart.eval x y) = some (periodEnd.eval x y))
    (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_nat_growth p family 28792194 cost (initial s) (by intro k; simp [cost,periodCost,Cost.eval]; omega) (growth h) m hm
#print axioms never_of_traces
''')
write('RF4563Never',header(['RF4563Join','RF4563Conclusion','Hybrid'])+'''open BB6.Agent13BlankDelay BB6.Agent6Hybrid

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := never_of_traces seedRun periodRun m hm

theorem weighted : Cover (WeightedBound 6024) p := by
  apply Cover.leaf
  intro m hm k d hh hd
  have H := never m hm (k+1)
  rw [hh.2] at H
  contradiction

theorem tableCover : Cover (WeightedBound 6024) (BB6Coverage.FAR.fromCodes [7,17,11,5,14,8,24,16,23,11,3,17]) := by
  apply sound 6024 _ (.covered p weighted)
  · decide +kernel
  · exact fromCodes_nohalt _
  · decide +kernel
#print axioms never
#print axioms weighted
#print axioms tableCover
''')
