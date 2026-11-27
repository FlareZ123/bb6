import SweepPumping
import FAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw47Binary907914
open BB6Coverage BB6Coverage.Agent31Pump

def ctr (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,if v then 1 else 4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => if v then some (some ⟨true,false,4⟩) else none
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => if v then none else some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def zz : List Bool := [false,false,false]
def oo : List Bool := [true,true,true]
def d1 : List Bool := [false,false,true]
def carry (k : Nat) (s : List Bool) : Z0 :=
  ⟨0,s.headD false :: (rep oo k ++ [false]),s.tail⟩
def fstate (k : Nat) (s : List Bool) : Z0 :=
  ⟨5,true :: (rep oo k++[false]),[false,true]++s⟩

theorem entry (v : Bool) : run0 (ctr v) 12 ⟨0,[],[]⟩ = some (carry 0 [false,false,true,false]) := by cases v <;> rfl

theorem carryOne (v : Bool) (k : Nat) (s : List Bool) :
    run0 (ctr v) 3 (carry k (d1++s)) = some (carry (k+1) s) := rfl
theorem carryZeroCons (v : Bool) (k : Nat) (s : List Bool) :
    run0 (ctr v) 10 (carry k (zz++false::s)) = some (fstate k (false::s)) := by cases v <;> rfl
theorem carryZeroNil (v : Bool) (k : Nat) :
    run0 (ctr v) 10 (carry k zz) = some (fstate k [false]) := by cases v <;> rfl
theorem carryEmpty (v : Bool) (k : Nat) :
    run0 (ctr v) 10 (carry k []) = some (fstate k [false]) := by cases v <;> rfl
theorem carryShort (v : Bool) (k : Nat) :
    run0 (ctr v) 10 (carry k [false]) = some (fstate k [false]) := by cases v <;> rfl
theorem fblock (v : Bool) (L R : List Bool) :
    run0 (ctr v) 3 ⟨5,oo++L,R⟩ = some ⟨5,L,zz++R⟩ := rfl
theorem fsweep (v : Bool) (k : Nat) (s : List Bool) :
    run0 (ctr v) (3*k) ⟨5,rep oo k++[false],s⟩ = some ⟨5,[false],rep zz k++s⟩ := by
  simpa only [List.nil_append] using sweepL (ctr v) 5 [] [] oo zz 3
    (by intro L R; simpa only [List.nil_append] using fblock v L R) k [false] s

theorem fhead (v : Bool) (k : Nat) (s : List Bool) :
    run0 (ctr v) 1 (fstate k s) = some ⟨5,rep oo k++[false],d1++s⟩ := rfl

theorem fend (v : Bool) (s : List Bool) :
    run0 (ctr v) 1 ⟨5,[false],s⟩ = some (carry 0 s) := rfl

theorem finish (v : Bool) (k : Nat) (s : List Bool) :
    run0 (ctr v) (1+3*k+1) (fstate k s) = some (carry 0 (rep zz k++d1++s)) := by
  simpa only [List.append_assoc] using join0 (join0 (fhead v k s) (fsweep v k (d1++s))) (fend v (rep zz k++(d1++s)))

inductive Good : List Bool → Prop where
  | empty : Good []
  | short : Good [false]
  | zero {s} : Good s → Good (zz++s)
  | one {s} : Good s → Good (d1++s)

theorem goodPad (k : Nat) {s : List Bool} (h : Good s) : Good (rep zz k++s) := by
  induction k with
  | zero => simpa [rep] using h
  | succ k ih => simpa only [rep,List.append_assoc] using Good.zero ih

theorem goodHead {s : List Bool} (h : Good s) : s = [] ∨ ∃ r, s = false::r := by
  cases h with
  | empty => exact Or.inl rfl
  | short => exact Or.inr ⟨[],rfl⟩
  | zero h => exact Or.inr ⟨_,rfl⟩
  | one h => exact Or.inr ⟨_,rfl⟩

theorem goodStep (v : Bool) (k : Nat) {s : List Bool} (h : Good s) :
    ∃ k' s' t, 0<t ∧ Good s' ∧ run0 (ctr v) t (carry k s) = some (carry k' s') := by
  cases h with
  | empty => exact ⟨0,_,_,by omega,by simpa only [List.append_assoc] using goodPad k (Good.one Good.short),join0 (carryEmpty v k) (finish v k [false])⟩
  | short => exact ⟨0,_,_,by omega,by simpa only [List.append_assoc] using goodPad k (Good.one Good.short),join0 (carryShort v k) (finish v k [false])⟩
  | one h => exact ⟨k+1,_,3,by decide,h,carryOne v k _⟩
  | @zero s h =>
    rcases goodHead h with rfl | ⟨r,rfl⟩
    · exact ⟨0,_,_,by omega,by simpa only [List.append_assoc] using goodPad k (Good.one Good.short),join0 (carryZeroNil v k) (finish v k [false])⟩
    · exact ⟨0,_,_,by omega,by simpa only [List.append_assoc] using goodPad k (Good.one h),join0 (carryZeroCons v k r) (finish v k (false::r))⟩

theorem arbitrarilyLive (v : Bool) (n : Nat) :
    ∃ k s t, n ≤ t ∧ Good s ∧ run0 (ctr v) t ⟨0,[],[]⟩ = some (carry k s) := by
  induction n with
  | zero => exact ⟨0,_,12,by decide,Good.one Good.short,entry v⟩
  | succ n ih =>
    obtain ⟨k,s,t,ht,hg,hr⟩ := ih
    obtain ⟨k',s',d,hd,hg',hs⟩ := goodStep v k hg
    exact ⟨k',s',t+d,by omega,hg',join0 hr hs⟩
theorem never (v : Bool) (m : Machine) (hm : compatible (ctr v) m) : NeverHalts m := by
  intro n
  obtain ⟨k,c,t,ht,_,hr⟩ := arbitrarilyLive v n
  have hz : (Agent50Zipper.zrun (ctr v) t start).map project = some (carry k c) :=
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
end BB6.Agent2Raw47Binary907914
