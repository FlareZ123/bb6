import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B0LAC1REM292
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
def P : List Bool := [true,true,true,true,true]
def Z : List Bool := [false,false,false,false,false]
def O : List Bool := [false,false,false,true,false]
def T : List Bool := [false,false,false,true]
def A (k : Nat) (R : List Bool) : Z0 := ⟨0,[false]++rep P k++[false],R⟩
def F (k : Nat) (R : List Bool) : Z0 := ⟨5,rep P k++[false],false::R⟩
inductive Good : List Bool → Prop where
  | terminal : Good T
  | zero {R} : Good R → Good (Z++R)
  | one {R} : Good R → Good (O++R)
inductive Inv : Z0 → Prop where
  | a k R : Good R → Inv (A k R)
  | empty k : Inv (A k [])
  | f k R : Good R → Inv (F k R)
private theorem aEnd (k : Nat) : run0 table 11 (A k T) = some (A (k+1) []) := by rfl
private theorem aOne (k : Nat) (R : List Bool) : run0 table 11 (A k (O++R)) = some (A (k+1) R) := by rfl
private theorem aZero (k : Nat) (R : List Bool) : run0 table 15 (A k (Z++R)) = some (F k (O++R)) := by rfl
private theorem aEmpty (k : Nat) : run0 table 15 (A k []) = some (F k T) := by rfl
private theorem fPop (k : Nat) (R : List Bool) : run0 table 5 (F (k+1) R) = some (F k (Z++R)) := by rfl
private theorem fReturn (R : List Bool) : run0 table 1 (F 0 R) = some (A 0 R) := by rfl
private theorem first : run0 table 16 ⟨0,[],[]⟩ = some (A 0 T) := by rfl
private theorem advance (z : Z0) (h : Inv z) : ∃ k z', 0<k ∧ run0 table k z=some z' ∧ Inv z' := by
  cases h with
  | a k R g => cases g with
    | terminal => exact ⟨11,_,by decide,aEnd k,.empty _⟩
    | zero g => exact ⟨15,_,by decide,aZero k _,.f _ _ (.one g)⟩
    | one g => exact ⟨11,_,by decide,aOne k _,.a _ _ g⟩
  | empty k => exact ⟨15,_,by decide,aEmpty k,.f _ _ .terminal⟩
  | f k R g => cases k with
    | zero => exact ⟨1,_,by decide,fReturn R,.a _ _ g⟩
    | succ k => exact ⟨5,_,by decide,fPop k R,.f _ _ (.zero g)⟩
theorem live_prefix (n : Nat) : ∃ t z, n≤t ∧ run0 table t ⟨0,[],[]⟩=some z ∧ Inv z := by
  induction n with
  | zero => exact ⟨16,_,by decide,first,.a _ _ .terminal⟩
  | succ n ih =>
    obtain ⟨t,z,ht,hr,hi⟩ := ih
    obtain ⟨k,z',hk,h,hi'⟩ := advance z hi
    exact ⟨t+k,z',by omega,join0 hr h,hi'⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr,hi⟩ := live_prefix n
  have hz : (zrun table t start).map project = some z :=
    (run_project table t start).trans hr
  cases hZ : zrun table t start with
  | none => simp [hZ] at hz
  | some z' =>
    have H := zrun_sound table m hm t start z' hZ
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl
#print axioms live_prefix
#print axioms never
end BB6.Agent25Raw43B0LAC1REM292
