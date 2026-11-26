import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39LE5883
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | _,_ => none

abbrev U : List Bool := [false,true,true]
abbrev Z : List Bool := [true,false,true]
abbrev P : List Bool := [false,false,true]
abbrev Q : List Bool := [true,true,false]
abbrev T : List Bool := [false,true,false]
abbrev base : List Bool := [false,true,true,false,false]
def frame (i : Nat) := rep U i ++ base
def F (i : Nat) (R : List Bool) : Z0 := ⟨5,frame i,R⟩

inductive Digits : List Bool → Prop
  | end1 : Digits [true]
  | end0 : Digits [false]
  | d0 {R} : Digits R → Digits (Z ++ R)
  | d1 {R} : Digits R → Digits (P ++ R)
  | d2 {R} : Digits R → Digits (Q ++ R)
  | d3 {R} : Digits R → Digits (T ++ R)

private theorem prepend (i : Nat) {R} (h : Digits R) : Digits (rep Z i ++ R) := by
  induction i with
  | zero => exact h
  | succ i ih => simpa only [rep,List.append_assoc] using Digits.d0 ih

private theorem carry (i : Nat) (R : List Bool) :
    run0 table 3 (F i (T ++ R)) = some (F (i+1) R) := by
  cases i with
  | zero => rfl
  | succ i => rfl

private theorem sweepOne (L R : List Bool) :
    run0 table 3 ⟨4,U++L,R⟩ = some ⟨4,L,Z++R⟩ := by rfl

private theorem finish (R : List Bool) :
    run0 table 24 ⟨4,base,R⟩ = some (F 0 R) := by rfl

private theorem reset (i : Nat) (R : List Bool) :
    run0 table (3*i+24) ⟨4,frame i,R⟩ = some (F 0 (rep Z i ++ R)) := by
  have hs := sweepL table 4 [] [] U Z 3 (by simpa using sweepOne) i base R
  have h := join0 hs (finish (rep Z i ++ R))
  simpa only [frame,List.nil_append] using h

private theorem change0 (i : Nat) (R : List Bool) :
    run0 table 2 (F i (Z++R)) = some ⟨4,frame i,P++R⟩ := by cases i <;> rfl
private theorem change1 (i : Nat) (R : List Bool) :
    run0 table 6 (F i (P++R)) = some ⟨4,frame i,Q++R⟩ := by cases i <;> rfl
private theorem change2 (i : Nat) (R : List Bool) :
    run0 table 2 (F i (Q++R)) = some ⟨4,frame i,T++R⟩ := by cases i <;> rfl
private theorem terminal1 (i : Nat) :
    run0 table 2 (F i [true]) = some ⟨4,frame i,[false]⟩ := by cases i <;> rfl
private theorem terminal0 (i : Nat) :
    run0 table 10 (F i [false]) = some ⟨4,frame i,T++[true]⟩ := by cases i <;> rfl

/-- Every F visit is live and advances to another F visit after positive time.
    The finite digit word is an unrestricted base-four counter, not a fixed-width guess. -/
theorem nextVisit (i : Nat) {R : List Bool} (h : Digits R) :
    ∃ k j S, 0 < k ∧ Digits S ∧ run0 table k (F i R) = some (F j S) := by
  cases h with
  | end1 => exact ⟨_,0,_,by omega,prepend i .end0,join0 (terminal1 i) (reset i _)⟩
  | end0 => exact ⟨_,0,_,by omega,prepend i (.d3 .end1),join0 (terminal0 i) (reset i _)⟩
  | d0 h => exact ⟨_,0,_,by omega,prepend i (.d1 h),join0 (change0 i _) (reset i _)⟩
  | d1 h => exact ⟨_,0,_,by omega,prepend i (.d2 h),join0 (change1 i _) (reset i _)⟩
  | d2 h => exact ⟨_,0,_,by omega,prepend i (.d3 h),join0 (change2 i _) (reset i _)⟩
  | d3 h => exact ⟨3,i+1,_,by decide,h,carry i _⟩

private theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (F 0 [true]) := by rfl

theorem live (n : Nat) : ∃ k i R, n ≤ k ∧ Digits R ∧ run0 table k ⟨0,[],[]⟩ = some (F i R) := by
  induction n with
  | zero => exact ⟨14,0,[true],by decide,.end1,entry⟩
  | succ n ih =>
    obtain ⟨k,i,R,hk,hd,hr⟩ := ih
    obtain ⟨t,j,S,ht,hs,he⟩ := nextVisit i hd
    exact ⟨k+t,j,S,by omega,hs,join0 hr he⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,i,R,ht,_,hr⟩ := live n
  have hz : (BB6Coverage.Agent50Zipper.zrun table t start).map project = some (F i R) :=
    (run_project table t start).trans hr
  cases h : BB6Coverage.Agent50Zipper.zrun table t start with
  | none => simp [h] at hz
  | some z =>
    have H := BB6Coverage.Agent50Zipper.zrun_sound table m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms nextVisit
#print axioms never
end BB6.Agent11Raw39LE5883
