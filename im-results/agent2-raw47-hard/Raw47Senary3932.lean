import SweepPumping
import FAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw47Senary3932
open BB6Coverage BB6Coverage.Agent31Pump

def ctr : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def ones : List Bool := [true,true,true,true,true]
def d0 : List Bool := [false,false,false,false,false]
def cfg (k : Nat) (s : List Bool) : Z0 := ⟨0,[false]++rep ones k++[false],s⟩
def fcfg (k : Nat) (s : List Bool) : Z0 := ⟨5,rep ones k++[false],s⟩

theorem fblock (L R : List Bool) :
    run0 ctr 5 ⟨5,ones++L,R⟩ = some ⟨5,L,d0++R⟩ := rfl

theorem fsweep (k : Nat) (s : List Bool) :
    run0 ctr (5*k) (fcfg k s) = some ⟨5,[false],rep d0 k++s⟩ := by
  simpa only [fcfg,List.nil_append] using sweepL ctr 5 [] [] ones d0 5 (by intro L R; simpa only [List.nil_append] using fblock L R) k [false] s

theorem zero_comm (k : Nat) : rep d0 k ++ [false] = [false] ++ rep d0 k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rep,List.append_assoc,ih]; rfl

theorem fend (k : Nat) (s : List Bool) :
    run0 ctr 1 ⟨5,[false],rep d0 k++[false]++s⟩ = some (cfg 0 (rep d0 k++s)) := by
  rw [zero_comm k,List.append_assoc]
  rfl

theorem finish (k : Nat) (s : List Bool) :
    run0 ctr (5*k+1) (fcfg k ([false]++s)) = some (cfg 0 (rep d0 k++s)) := by
  exact join0 (fsweep k ([false]++s)) (by simpa only [List.append_assoc] using fend k s)

def d1 : List Bool := [true,false,true,false,false]
def d2 : List Bool := [false,true,true,false,false]
def d3 : List Bool := [false,false,false,true,false]
def d4 : List Bool := [true,false,true,true,false]
def d5 : List Bool := [false,true,true,true,false]
def t0 : List Bool := []
def t1 : List Bool := [true,false,true]
def t2 : List Bool := [false,true,true]
def t3 : List Bool := [false,false,false,true]
def t4 : List Bool := [true,false,true,true]
def t5 : List Bool := [false,true,true,true]

theorem entry : run0 ctr 10 ⟨0,[],[]⟩ = some (cfg 0 t1) := rfl

theorem dStep0 (k : Nat) (tail : List Bool) :
    run0 ctr (9+(5*k+1)) (cfg k (d0++tail)) = some (cfg 0 (rep d0 k++(d1++tail))) := by
  have h : run0 ctr 9 (cfg k (d0++tail)) = some (fcfg k ([false]++(d1++tail))) := rfl
  exact join0 h (finish k (d1++tail))

theorem dStep1 (k : Nat) (tail : List Bool) :
    run0 ctr (5+(5*k+1)) (cfg k (d1++tail)) = some (cfg 0 (rep d0 k++(d2++tail))) := by
  have h : run0 ctr 5 (cfg k (d1++tail)) = some (fcfg k ([false]++(d2++tail))) := rfl
  exact join0 h (finish k (d2++tail))

theorem dStep2 (k : Nat) (tail : List Bool) :
    run0 ctr (11+(5*k+1)) (cfg k (d2++tail)) = some (cfg 0 (rep d0 k++(d3++tail))) := by
  have h : run0 ctr 11 (cfg k (d2++tail)) = some (fcfg k ([false]++(d3++tail))) := rfl
  exact join0 h (finish k (d3++tail))

theorem dStep3 (k : Nat) (tail : List Bool) :
    run0 ctr (9+(5*k+1)) (cfg k (d3++tail)) = some (cfg 0 (rep d0 k++(d4++tail))) := by
  have h : run0 ctr 9 (cfg k (d3++tail)) = some (fcfg k ([false]++(d4++tail))) := rfl
  exact join0 h (finish k (d4++tail))

theorem dStep4 (k : Nat) (tail : List Bool) :
    run0 ctr (5+(5*k+1)) (cfg k (d4++tail)) = some (cfg 0 (rep d0 k++(d5++tail))) := by
  have h : run0 ctr 5 (cfg k (d4++tail)) = some (fcfg k ([false]++(d5++tail))) := rfl
  exact join0 h (finish k (d5++tail))

theorem dStep5 (k : Nat) (tail : List Bool) :
    run0 ctr 7 (cfg k (d5++tail)) = some (cfg (k+1) tail) := rfl

theorem tStep0 (k : Nat) :
    run0 ctr (9+(5*k+1)) (cfg k t0) = some (cfg 0 (rep d0 k++t1)) := by
  have h : run0 ctr 9 (cfg k t0) = some (fcfg k ([false]++t1)) := rfl
  exact join0 h (finish k t1)

theorem tStep1 (k : Nat) :
    run0 ctr (5+(5*k+1)) (cfg k t1) = some (cfg 0 (rep d0 k++t2)) := by
  have h : run0 ctr 5 (cfg k t1) = some (fcfg k ([false]++t2)) := rfl
  exact join0 h (finish k t2)

theorem tStep2 (k : Nat) :
    run0 ctr (11+(5*k+1)) (cfg k t2) = some (cfg 0 (rep d0 k++t3)) := by
  have h : run0 ctr 11 (cfg k t2) = some (fcfg k ([false]++t3)) := rfl
  exact join0 h (finish k t3)

theorem tStep3 (k : Nat) :
    run0 ctr (9+(5*k+1)) (cfg k t3) = some (cfg 0 (rep d0 k++t4)) := by
  have h : run0 ctr 9 (cfg k t3) = some (fcfg k ([false]++t4)) := rfl
  exact join0 h (finish k t4)

theorem tStep4 (k : Nat) :
    run0 ctr (5+(5*k+1)) (cfg k t4) = some (cfg 0 (rep d0 k++t5)) := by
  have h : run0 ctr 5 (cfg k t4) = some (fcfg k ([false]++t5)) := rfl
  exact join0 h (finish k t5)

theorem tStep5 (k : Nat) :
    run0 ctr 7 (cfg k t5) = some (cfg (k+1) []) := rfl

inductive Good : List Bool → Prop where
  | term0 : Good t0
  | term1 : Good t1
  | term2 : Good t2
  | term3 : Good t3
  | term4 : Good t4
  | term5 : Good t5
  | digit0 {s} : Good s → Good (d0++s)
  | digit1 {s} : Good s → Good (d1++s)
  | digit2 {s} : Good s → Good (d2++s)
  | digit3 {s} : Good s → Good (d3++s)
  | digit4 {s} : Good s → Good (d4++s)
  | digit5 {s} : Good s → Good (d5++s)

theorem goodPad (k : Nat) {s : List Bool} (h : Good s) : Good (rep d0 k++s) := by
  induction k with
  | zero => simpa [rep] using h
  | succ k ih => simpa only [rep,List.append_assoc] using Good.digit0 ih

theorem goodStep (k : Nat) {s : List Bool} (h : Good s) :
    ∃ k' s' t, 0<t ∧ Good s' ∧ run0 ctr t (cfg k s) = some (cfg k' s') := by
  cases h with
  | term0 => exact ⟨0,_,_,by omega,goodPad k Good.term1,tStep0 k⟩
  | term1 => exact ⟨0,_,_,by omega,goodPad k Good.term2,tStep1 k⟩
  | term2 => exact ⟨0,_,_,by omega,goodPad k Good.term3,tStep2 k⟩
  | term3 => exact ⟨0,_,_,by omega,goodPad k Good.term4,tStep3 k⟩
  | term4 => exact ⟨0,_,_,by omega,goodPad k Good.term5,tStep4 k⟩
  | term5 => exact ⟨k+1,[],7,by omega,Good.term0,tStep5 k⟩
  | digit0 h => exact ⟨0,_,_,by omega,goodPad k (Good.digit1 h),dStep0 k _⟩
  | digit1 h => exact ⟨0,_,_,by omega,goodPad k (Good.digit2 h),dStep1 k _⟩
  | digit2 h => exact ⟨0,_,_,by omega,goodPad k (Good.digit3 h),dStep2 k _⟩
  | digit3 h => exact ⟨0,_,_,by omega,goodPad k (Good.digit4 h),dStep3 k _⟩
  | digit4 h => exact ⟨0,_,_,by omega,goodPad k (Good.digit5 h),dStep4 k _⟩
  | digit5 h => exact ⟨k+1,_,7,by omega,h,dStep5 k _⟩

theorem arbitrarilyLive (n : Nat) :
    ∃ k s t, n ≤ t ∧ Good s ∧ run0 ctr t ⟨0,[],[]⟩ = some (cfg k s) := by
  induction n with
  | zero => exact ⟨0,t1,10,by omega,Good.term1,entry⟩
  | succ n ih =>
    obtain ⟨k,s,t,ht,hg,hr⟩ := ih
    obtain ⟨k',s',d,hd,hg',hs⟩ := goodStep k hg
    exact ⟨k',s',t+d,by omega,hg',join0 hr hs⟩

theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m := by
  intro n
  obtain ⟨k,s,t,ht,_,hr⟩ := arbitrarilyLive n
  have hz : (Agent50Zipper.zrun ctr t start).map project = some (cfg k s) :=
    (run_project ctr t start).trans hr
  cases h : Agent50Zipper.zrun ctr t start with
  | none => simp [h] at hz
  | some z =>
    have H := Agent50Zipper.zrun_sound ctr m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms goodStep
#print axioms never
end BB6.Agent2Raw47Senary3932
