import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B1LBC1RAGrowth
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,if v then 5 else 4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => if v then none else some (some ⟨true,false,1⟩)
  | 4,true => some (some (if v then ⟨true,true,3⟩ else ⟨true,true,5⟩))
  | 5,false => if v then some (some ⟨true,false,1⟩) else none
  | 5,true => some (some (if v then ⟨true,true,4⟩ else ⟨true,true,3⟩))
  | _,_ => none

def ones (n : Nat) : List Bool := List.replicate n true
def S (n : Nat) : Z0 := ⟨0,[true,true,true],ones n⟩
private theorem sweep1 (v : Bool) (l r : Nat) :
    run0 (table v) 7 ⟨0,ones (l+1),ones (r+5)⟩ = some ⟨0,ones (l+1+5),ones r⟩ := by cases v <;> rfl
private theorem sweep (v : Bool) (k l r : Nat) :
    run0 (table v) (7*k) ⟨0,ones (l+1),ones (5*k+r)⟩ = some ⟨0,ones (l+1+5*k),ones r⟩ := by
  induction k generalizing l with
  | zero => simp [run0]
  | succ k ih =>
    have h1 := sweep1 v l (5*k+r)
    have h2 := ih (l+5)
    rw [show l+5+1=l+1+5 by omega] at h2
    have h := join0 h1 h2
    rw [show 7+7*k=7*(k+1) by omega, show 5*k+r+5=5*(k+1)+r by omega, show l+1+5+5*k=l+1+5*(k+1) by omega] at h
    exact h
private theorem left (v : Bool) (n : Nat) (R : List Bool) :
    run0 (table v) n ⟨1,ones n,R⟩ = some ⟨1,[],ones n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 : run0 (table v) 1 ⟨1,ones (n+1),R⟩ = some ⟨1,ones n,true::R⟩ := by rfl
    have h := join0 h1 (ih (true::R))
    rw [show 1+n=n+1 by omega] at h
    have hr : ones (n+1)++R = ones n++true::R := by rw [show ones (n+1)=ones n++[true] by exact List.replicate_succ', List.append_assoc]; rfl
    rw [hr]
    exact h
private theorem reset (v : Bool) (l : Nat) :
    run0 (table v) (l+3+2) ⟨1,ones (l+3),[true]⟩ = some (S (l+2)) := by
  have h := left v (l+3) [true]
  have hr : ones (l+3)++[true]=ones (l+3+1) := List.replicate_succ'.symm
  rw [hr] at h
  have h2 : run0 (table v) 2 ⟨1,[],ones (l+3+1)⟩ = some (S (l+2)) := by rfl
  exact join0 h h2
private theorem term0 (v : Bool) (l : Nat) : run0 (table v) 2 ⟨0,ones (l+3),ones 0⟩ = some ⟨1,ones (l+3),[true]⟩ := by cases v <;> rfl
private theorem term2 (v : Bool) (l : Nat) : run0 (table v) 19 ⟨0,ones (l+3),ones 2⟩ = some ⟨1,ones (l+7+3),[true]⟩ := by cases v <;> rfl
private theorem term3 (v : Bool) (l : Nat) : run0 (table v) 38 ⟨0,ones (l+3),ones 3⟩ = some ⟨1,ones (l+12+3),[true]⟩ := by cases v <;> rfl
private theorem term4 (v : Bool) (l : Nat) : run0 (table v) 18 ⟨0,ones (l+3),ones 4⟩ = some ⟨1,ones (l+8+3),[true]⟩ := by cases v <;> rfl
private theorem sweepS (v : Bool) (k r : Nat) : run0 (table v) (7*k) (S (5*k+r)) = some ⟨0,ones (5*k+3),ones r⟩ := by
  have h := sweep v k 2 r
  rw [show 2+1+5*k=5*k+3 by omega] at h
  exact h

theorem return0 (v : Bool) (k : Nat) : run0 (table v) (7*k+2+(5*k+3+2)) (S (5*k)) = some (S (5*k+2)) := by
  have h := join0 (join0 (sweepS v k 0) (term0 v (5*k))) (reset v (5*k))
  simpa using h
theorem return2 (v : Bool) (k : Nat) : run0 (table v) (7*k+19+(5*k+7+3+2)) (S (5*k+2)) = some (S (5*(k+1)+4)) := by
  have h := join0 (join0 (sweepS v k 2) (term2 v (5*k))) (reset v (5*k+7))
  rw [show 5*k+7+2=5*(k+1)+4 by omega] at h
  exact h
theorem return3 (v : Bool) (k : Nat) : run0 (table v) (7*k+38+(5*k+12+3+2)) (S (5*k+3)) = some (S (5*(k+2)+4)) := by
  have h := join0 (join0 (sweepS v k 3) (term3 v (5*k))) (reset v (5*k+12))
  rw [show 5*k+12+2=5*(k+2)+4 by omega] at h
  exact h
theorem return4 (v : Bool) (k : Nat) : run0 (table v) (7*k+18+(5*k+8+3+2)) (S (5*k+4)) = some (S (5*(k+2))) := by
  have h := join0 (join0 (sweepS v k 4) (term4 v (5*k))) (reset v (5*k+8))
  rw [show 5*k+8+2=5*(k+2) by omega] at h
  exact h
theorem first (v : Bool) : run0 (table v) 17 ⟨0,[],[]⟩ = some (S 3) := by cases v <;> rfl
theorem live_prefix (v : Bool) (n : Nat) : ∃ t k r, n ≤ t ∧ (r=0 ∨ r=2 ∨ r=3 ∨ r=4) ∧ run0 (table v) t ⟨0,[],[]⟩ = some (S (5*k+r)) := by
  induction n with
  | zero => exact ⟨17,0,3,by decide,by decide,first v⟩
  | succ n ih =>
    obtain ⟨t,k,r,ht,hr,h⟩ := ih
    rcases hr with rfl|rfl|rfl|rfl
    · exact ⟨_,k,2,by omega,by decide,join0 h (return0 v k)⟩
    · exact ⟨_,k+1,4,by omega,by decide,join0 h (return2 v k)⟩
    · exact ⟨_,k+2,4,by omega,by decide,join0 h (return3 v k)⟩
    · exact ⟨_,k+2,0,by omega,by decide,join0 h (return4 v k)⟩
theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  intro n
  obtain ⟨t,k,r,ht,hr,h⟩ := live_prefix v n
  have hz : (zrun (table v) t start).map project = some (S (5*k+r)) :=
    (run_project (table v) t start).trans h
  cases hZ : zrun (table v) t start with
  | none => simp [hZ] at hz
  | some z =>
    have H := zrun_sound (table v) m hm t start z hZ
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl
#print axioms live_prefix
#print axioms never
end BB6.Agent25Raw43B1LBC1RAGrowth
