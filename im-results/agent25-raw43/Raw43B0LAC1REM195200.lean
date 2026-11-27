import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B0LAC1REM195200
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper
def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨v,true,5⟩)
  | 5,false => some (some ⟨!v,true,0⟩)
  | _,_ => none

def K : List Bool := [false,false,false,false,false,false,false,true]
def B : List Bool := [false,false,false,false,false,true]
def Q : List Bool := [false,false,false,true]
def T : List Bool := [false,true]
def O : List Bool := [true,true,true,true,true,false]
def pref (v : Bool) : List Bool := if v then [false,false] else [false,true,false]
def endL (v : Bool) : List Bool := if v then [true,true,true,true,true] else [true,true,true,true]
def headL (v : Bool) : List Bool := if v then [true,false] else [true,true,false]
def Root (R : List Bool) : Z0 := ⟨0,[true],K++R⟩
def Right (v : Bool) (L R : List Bool) : Z0 := ⟨0,pref v++L,Q++R⟩
def Left (v : Bool) (L R : List Bool) : Z0 := ⟨0,headL v++L,K++R⟩
inductive Good : List Bool → Prop where
  | nil : Good []
  | tail : Good T
  | block {R} : Good R → Good (B++R)
inductive Stack (v : Bool) : List Bool → Prop where
  | base : Stack v (endL v)
  | block {L} : Stack v L → Stack v (O++L)
inductive Inv (v : Bool) : Z0 → Prop where
  | root R : Good R → Inv v (Root R)
  | right L R : Stack v L → Good R → Inv v (Right v L R)
  | left L R : Stack v L → Good R → Inv v (Left v L R)

private theorem enter (v : Bool) (R : List Bool) :
    run0 (table v) 26 (Root R) = some (Right v (endL v) R) := by cases v <;> rfl
private theorem push (v : Bool) (L R : List Bool) :
    run0 (table v) 12 (Right v L (B++R)) = some (Right v (O++L) R) := by cases v <;> rfl
private theorem turn0 (v : Bool) (L : List Bool) :
    run0 (table v) (if v then 44 else 46) (Right v L []) = some (Left v L T) := by cases v <;> rfl
private theorem turn1 (v : Bool) (L : List Bool) :
    run0 (table v) (if v then 30 else 32) (Right v L T) = some (Left v L []) := by cases v <;> rfl
private theorem pop (v : Bool) (L R : List Bool) :
    run0 (table v) (if v then 18 else 20) (Left v (O++L) R) = some (Left v L (B++R)) := by cases v <;> rfl
private theorem finish (v : Bool) (R : List Bool) :
    run0 (table v) (if v then 18 else 20) (Left v (endL v) R) = some (Root (B++R)) := by cases v <;> rfl
private theorem first (v : Bool) :
    run0 (table v) (if v then 58 else 60) ⟨0,[],[]⟩ = some (Root []) := by cases v <;> rfl

private theorem advance (v : Bool) (z : Z0) (h : Inv v z) :
    ∃ k z', 0 < k ∧ run0 (table v) k z = some z' ∧ Inv v z' := by
  cases h with
  | root R g => exact ⟨26,_,by decide,enter v R,.right _ _ .base g⟩
  | right L R s g => cases g with
    | nil => exact ⟨_,_,by cases v <;> decide,turn0 v L,.left _ _ s .tail⟩
    | tail => exact ⟨_,_,by cases v <;> decide,turn1 v L,.left _ _ s .nil⟩
    | block g => exact ⟨12,_,by decide,push v L _,.right _ _ (.block s) g⟩
  | left L R s g => cases s with
    | base => exact ⟨_,_,by cases v <;> decide,finish v R,.root _ (.block g)⟩
    | block s => exact ⟨_,_,by cases v <;> decide,pop v _ R,.left _ _ s (.block g)⟩
theorem live_prefix (v : Bool) (n : Nat) :
    ∃ t z, n≤t ∧ run0 (table v) t ⟨0,[],[]⟩=some z ∧ Inv v z := by
  induction n with
  | zero => exact ⟨_,_,by omega,first v,.root _ .nil⟩
  | succ n ih =>
    obtain ⟨t,z,ht,hr,hi⟩ := ih
    obtain ⟨k,z',hk,h,hi'⟩ := advance v z hi
    exact ⟨t+k,z',by omega,join0 hr h,hi'⟩
theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr,hi⟩ := live_prefix v n
  have hz : (zrun (table v) t start).map project = some z :=
    (run_project (table v) t start).trans hr
  cases hZ : zrun (table v) t start with
  | none => simp [hZ] at hz
  | some z' =>
    have H := zrun_sound (table v) m hm t start z' hZ
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl
#print axioms live_prefix
#print axioms never
end BB6.Agent25Raw43B0LAC1REM195200
