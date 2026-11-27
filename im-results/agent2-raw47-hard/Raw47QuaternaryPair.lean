import SweepPumping
import FAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw47QuaternaryPair
open BB6Coverage BB6Coverage.Agent31Pump

-- true = 27039, false = 27050

def ctr (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => if v then some (some ⟨true,false,2⟩) else none
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => if v then none else some (some ⟨true,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,if v then 0 else 1⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

def ones : List Bool := [true,true,true,true,true]
def d0 : List Bool := [false,false,false,false,false]
def d1 : List Bool := [false,true,false,false,false]
def d2 : List Bool := [false,false,false,true,false]
def d3 : List Bool := [false,true,false,true,false]
def t0 : List Bool := []
def t1 : List Bool := [false,true,false]
def t2 : List Bool := [false,false,false,true]
def t3 : List Bool := [false,true,false,true]
def cfg (k : Nat) (s : List Bool) : Z0 := ⟨0,[false,true,true,true]++rep ones k++[false,false],s⟩
def ecfg (k : Nat) (s : List Bool) : Z0 := ⟨4,ones++rep ones k++[false,false],s⟩

theorem entry (v : Bool) : run0 (ctr v) 23 ⟨0,[],[]⟩ = some (cfg 0 []) := by cases v <;> rfl

theorem eblock (v : Bool) (L R : List Bool) :
    run0 (ctr v) 5 ⟨4,ones++L,R⟩ = some ⟨4,L,d0++R⟩ := rfl

theorem esweep (v : Bool) (k : Nat) (s : List Bool) :
    run0 (ctr v) (5*k) (ecfg k s) = some ⟨4,ones++[false,false],rep d0 k++s⟩ := by
  simpa only [ecfg,List.nil_append,List.append_assoc,← rep_snoc ones k] using sweepL (ctr v) 4 [] [] ones d0 5 (by intro L R; simpa only [List.nil_append] using eblock v L R) k (ones++[false,false]) s

theorem zero_comm (k : Nat) : rep d0 k ++ [false] = [false] ++ rep d0 k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rep,List.append_assoc,ih]; rfl

theorem efixed (v : Bool) (s : List Bool) :
    run0 (ctr v) 25 ⟨4,ones++[false,false],s⟩ = some (cfg 0 ([false]++s)) := by cases v <;> rfl

theorem finish (v : Bool) (k : Nat) (s : List Bool) :
    run0 (ctr v) (5*k+25) (ecfg k s) = some (cfg 0 (rep d0 k++[false]++s)) := by
  have h := join0 (esweep v k s) (efixed v (rep d0 k++s))
  rw [zero_comm k,List.append_assoc]
  exact h

theorem dStep0 (v : Bool) (k : Nat) (tail : List Bool) :
    run0 (ctr v) (13+(5*k+25)) (cfg k (d0++tail)) = some (cfg 0 (rep d0 k++(d1++tail))) := by
  have h : run0 (ctr v) 13 (cfg k (d0++tail)) = some (ecfg k ([true,false,false,false]++tail)) := by cases v <;> rfl
  simpa only [List.append_assoc, d1, List.cons_append, List.nil_append] using join0 h (finish v k ([true,false,false,false]++tail))

theorem dStep1 (v : Bool) (k : Nat) (tail : List Bool) :
    run0 (ctr v) (9+(5*k+25)) (cfg k (d1++tail)) = some (cfg 0 (rep d0 k++(d2++tail))) := by
  have h : run0 (ctr v) 9 (cfg k (d1++tail)) = some (ecfg k ([false,false,true,false]++tail)) := by cases v <;> rfl
  simpa only [List.append_assoc, d2, List.cons_append, List.nil_append] using join0 h (finish v k ([false,false,true,false]++tail))

theorem dStep2 (v : Bool) (k : Nat) (tail : List Bool) :
    run0 (ctr v) (13+(5*k+25)) (cfg k (d2++tail)) = some (cfg 0 (rep d0 k++(d3++tail))) := by
  have h : run0 (ctr v) 13 (cfg k (d2++tail)) = some (ecfg k ([true,false,true,false]++tail)) := by cases v <;> rfl
  simpa only [List.append_assoc, d3, List.cons_append, List.nil_append] using join0 h (finish v k ([true,false,true,false]++tail))

theorem dStep3 (v : Bool) (k : Nat) (tail : List Bool) :
    run0 (ctr v) 5 (cfg k (d3++tail)) = some (cfg (k+1) tail) := by cases v <;> rfl

theorem tStep0 (v : Bool) (k : Nat) :
    run0 (ctr v) (13+(5*k+25)) (cfg k t0) = some (cfg 0 (rep d0 k++t1)) := by
  have h : run0 (ctr v) 13 (cfg k t0) = some (ecfg k ([true,false])) := by cases v <;> rfl
  simpa only [List.append_assoc, t1, List.cons_append, List.nil_append] using join0 h (finish v k ([true,false]))

theorem tStep1 (v : Bool) (k : Nat) :
    run0 (ctr v) (9+(5*k+25)) (cfg k t1) = some (cfg 0 (rep d0 k++t2)) := by
  have h : run0 (ctr v) 9 (cfg k t1) = some (ecfg k ([false,false,true])) := by cases v <;> rfl
  simpa only [List.append_assoc, t2, List.cons_append, List.nil_append] using join0 h (finish v k ([false,false,true]))

theorem tStep2 (v : Bool) (k : Nat) :
    run0 (ctr v) (13+(5*k+25)) (cfg k t2) = some (cfg 0 (rep d0 k++t3)) := by
  have h : run0 (ctr v) 13 (cfg k t2) = some (ecfg k ([true,false,true])) := by cases v <;> rfl
  simpa only [List.append_assoc, t3, List.cons_append, List.nil_append] using join0 h (finish v k ([true,false,true]))

theorem tStep3 (v : Bool) (k : Nat) :
    run0 (ctr v) 5 (cfg k t3) = some (cfg (k+1) []) := by cases v <;> rfl

inductive Good : List Bool → Prop where
  | term0 : Good t0
  | term1 : Good t1
  | term2 : Good t2
  | term3 : Good t3
  | digit0 {s} : Good s → Good (d0++s)
  | digit1 {s} : Good s → Good (d1++s)
  | digit2 {s} : Good s → Good (d2++s)
  | digit3 {s} : Good s → Good (d3++s)

theorem goodPad (k : Nat) {s : List Bool} (h : Good s) : Good (rep d0 k++s) := by
  induction k with
  | zero => simpa [rep] using h
  | succ k ih => simpa only [rep,List.append_assoc] using Good.digit0 ih

theorem goodStep (v : Bool) (k : Nat) {s : List Bool} (h : Good s) :
    ∃ k' s' t, 0<t ∧ Good s' ∧ run0 (ctr v) t (cfg k s) = some (cfg k' s') := by
  cases h with
  | term0 => exact ⟨0,_,_,by omega,goodPad k Good.term1,tStep0 v k⟩
  | term1 => exact ⟨0,_,_,by omega,goodPad k Good.term2,tStep1 v k⟩
  | term2 => exact ⟨0,_,_,by omega,goodPad k Good.term3,tStep2 v k⟩
  | term3 => exact ⟨k+1,[],5,by omega,Good.term0,tStep3 v k⟩
  | digit0 h => exact ⟨0,_,_,by omega,goodPad k (Good.digit1 h),dStep0 v k _⟩
  | digit1 h => exact ⟨0,_,_,by omega,goodPad k (Good.digit2 h),dStep1 v k _⟩
  | digit2 h => exact ⟨0,_,_,by omega,goodPad k (Good.digit3 h),dStep2 v k _⟩
  | digit3 h => exact ⟨k+1,_,5,by omega,h,dStep3 v k _⟩

theorem arbitrarilyLive (v : Bool) (n : Nat) :
    ∃ k s t, n ≤ t ∧ Good s ∧ run0 (ctr v) t ⟨0,[],[]⟩ = some (cfg k s) := by
  induction n with
  | zero => exact ⟨0,[],23,by omega,Good.term0,entry v⟩
  | succ n ih =>
    obtain ⟨k,s,t,ht,hg,hr⟩ := ih
    obtain ⟨k',s',d,hd,hg',hs⟩ := goodStep v k hg
    exact ⟨k',s',t+d,by omega,hg',join0 hr hs⟩

theorem never (v : Bool) (m : Machine) (hm : compatible (ctr v) m) : NeverHalts m := by
  intro n
  obtain ⟨k,s,t,ht,_,hr⟩ := arbitrarilyLive v n
  have hz : (Agent50Zipper.zrun (ctr v) t start).map project = some (cfg k s) :=
    (run_project (ctr v) t start).trans hr
  cases h : Agent50Zipper.zrun (ctr v) t start with
  | none => simp [h] at hz
  | some z =>
    have H := Agent50Zipper.zrun_sound (ctr v) m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms goodStep
#print axioms never
end BB6.Agent2Raw47QuaternaryPair
