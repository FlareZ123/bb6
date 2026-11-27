import SweepPumping
import FAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw47Ternary3312
open BB6Coverage BB6Coverage.Agent31Pump

def ctr : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def ones : List Bool := [true,true,true,true,true]
def d0 : List Bool := [false,false,false,false,false]
def d1 : List Bool := [false,false,true,false,false]
def d2 : List Bool := [false,false,true,true,true]
def short1 : List Bool := [false,false,true]
def cfg (k : Nat) (s : List Bool) : Z0 := ⟨0,[false]++rep ones k++[false],s⟩
def fcfg (k : Nat) (s : List Bool) : Z0 := ⟨5,rep ones k++[false],s⟩

theorem entry : run0 ctr 12 ⟨0,[],[]⟩ = some (cfg 0 short1) := rfl

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

theorem zeroStep (k : Nat) (s : List Bool) :
    run0 ctr (11+(5*k+1)) (cfg k (d0++s)) = some (cfg 0 (rep d0 k++d1++s)) := by
  have h : run0 ctr 11 (cfg k (d0++s)) = some (fcfg k ([false]++(d1++s))) := rfl
  simpa only [List.append_assoc] using join0 h (finish k (d1++s))

theorem oneStep (k : Nat) (s : List Bool) :
    run0 ctr (15+(5*k+1)) (cfg k (d1++s)) = some (cfg 0 (rep d0 k++d2++s)) := by
  have h : run0 ctr 15 (cfg k (d1++s)) = some (fcfg k ([false]++(d2++s))) := rfl
  simpa only [List.append_assoc] using join0 h (finish k (d2++s))

theorem twoStep (k : Nat) (s : List Bool) :
    run0 ctr 13 (cfg k (d2++s)) = some (cfg (k+1) s) := rfl

theorem emptyStep (k : Nat) :
    run0 ctr (11+(5*k+1)) (cfg k []) = some (cfg 0 (rep d0 k++short1)) := by
  have h : run0 ctr 11 (cfg k []) = some (fcfg k ([false]++short1)) := rfl
  exact join0 h (finish k short1)

theorem shortStep (k : Nat) :
    run0 ctr (15+(5*k+1)) (cfg k short1) = some (cfg 0 (rep d0 k++d2)) := by
  have h : run0 ctr 15 (cfg k short1) = some (fcfg k ([false]++d2)) := rfl
  exact join0 h (finish k d2)

inductive Good : List Bool → Prop where
  | empty : Good []
  | short : Good short1
  | zero {s} : Good s → Good (d0++s)
  | one {s} : Good s → Good (d1++s)
  | two {s} : Good s → Good (d2++s)

theorem goodPad (k : Nat) {s : List Bool} (h : Good s) : Good (rep d0 k++s) := by
  induction k with
  | zero => simpa [rep] using h
  | succ k ih => simpa only [rep,List.append_assoc] using Good.zero ih

theorem goodStep (k : Nat) {s : List Bool} (h : Good s) :
    ∃ k' s' t, 0<t ∧ Good s' ∧ run0 ctr t (cfg k s) = some (cfg k' s') := by
  cases h with
  | empty => exact ⟨0,_,_,by omega,goodPad k Good.short,emptyStep k⟩
  | short => exact ⟨0,_,_,by omega,goodPad k (by simpa only [List.append_nil] using Good.two Good.empty),shortStep k⟩
  | zero h => exact ⟨0,_,_,by omega,by simpa only [List.append_assoc] using goodPad k (Good.one h),zeroStep k _⟩
  | one h => exact ⟨0,_,_,by omega,by simpa only [List.append_assoc] using goodPad k (Good.two h),oneStep k _⟩
  | two h => exact ⟨k+1,_,13,by omega,h,twoStep k _⟩

theorem arbitrarilyLive (n : Nat) :
    ∃ k s t, n ≤ t ∧ Good s ∧ run0 ctr t ⟨0,[],[]⟩ = some (cfg k s) := by
  induction n with
  | zero => exact ⟨0,short1,12,by omega,Good.short,entry⟩
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
end BB6.Agent2Raw47Ternary3312
