import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B1REE1RDM44
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,true,3⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def P : Nat → List Bool
  | 0 => []
  | n+1 => true::false::P n
def Q : Nat → List Bool
  | 0 => []
  | n+1 => false::true::Q n

def A (k m : Nat) : Z0 := ⟨0,false::Q (2*k),P (2*m)⟩
def E (k : Nat) (R : List Bool) : Z0 := ⟨4,Q k,R⟩

theorem first (m : Nat) : run0 table 8 ⟨0,[],P (2*(m+1))⟩ = some (A 1 m) := by
  rw [show 2*(m+1)=2*m+2 by omega]
  rfl

theorem forward (k m : Nat) : run0 table 8 (A k (m+1)) = some (A (k+1) m) := by
  unfold A
  rw [show 2*(k+1)=2*k+2 by omega,show 2*(m+1)=2*m+2 by omega]
  rfl

theorem turn (k : Nat) : run0 table 11 (A k 0) = some (E (2*k+3) []) := by rfl

theorem sweep (n : Nat) (R : List Bool) : run0 table 2 (E (n+1) R) = some (E n (true::false::R)) := by rfl

theorem p_shift (n : Nat) (R : List Bool) : P n ++ true::false::R = P (n+1) ++ R := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [P,List.cons_append]; rw [ih]; rfl

theorem sweepAll (n : Nat) (R : List Bool) : run0 table (2*n) (E n R) = some (E 0 (P n++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have H := join0 (sweep n R) (ih (true::false::R))
    rw [p_shift] at H
    rw [show 2*(n+1)=2+2*n by omega]
    exact H

theorem finish (R : List Bool) : run0 table 2 (E 0 R) = some (⟨0,[],true::false::R⟩ : Z0) := by rfl

theorem back (k : Nat) : run0 table (4*k+19) (A k 0) = some (⟨0,[],P (2*(k+2))⟩ : Z0) := by
  have H := join0 (join0 (turn k) (sweepAll (2*k+3) [])) (finish (P (2*k+3)++[]))
  simp only [List.append_nil] at H
  rw [show 4*k+19=11+2*(2*k+3)+2 by omega,show 2*(k+2)=2*k+3+1 by omega]
  exact H

inductive Inv : Z0 → Prop
  | emp (m : Nat) : Inv ⟨0,[],P (2*(m+1))⟩
  | a (k m : Nat) : Inv (A k m)

theorem stepInv (z : Z0) (h : Inv z) : ∃ t z', 0<t ∧ run0 table t z=some z' ∧ Inv z' := by
  cases h with
  | emp m => exact ⟨8,_,by omega,first m,Inv.a 1 m⟩
  | a k m => cases m with
    | zero => exact ⟨4*k+19,_,by omega,back k,Inv.emp (k+1)⟩
    | succ m => exact ⟨8,_,by omega,forward k m,Inv.a (k+1) m⟩

theorem start : run0 table 19 ⟨0,[],[]⟩ = some (⟨0,[],P 4⟩ : Z0) := by rfl

theorem live (N : Nat) : ∃ t z, N≤t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ Inv z := by
  induction N with
  | zero => exact ⟨19,_,by omega,start,Inv.emp 1⟩
  | succ N ih =>
    obtain ⟨t,z,ht,hz,hi⟩ := ih
    obtain ⟨a,z',ha,hr,hi'⟩ := stepInv z hi
    exact ⟨t+a,z',by omega,join0 hz hr,hi'⟩

open BB6Coverage.Agent50Zipper

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr,_⟩ := live n
  let start : Z := ⟨0,0,[],[]⟩
  have hz : (zrun table t start).map project = some z :=
    (run_project table t start).trans hr
  cases hZ : zrun table t start with
  | none => simp [hZ] at hz
  | some z' =>
    have H := zrun_sound table m hm t start z' hZ
    have hb : embed start = blank := by
      unfold embed blank
      congr 1
      funext x
      unfold atCell start
      split <;> rfl
    rw [hb] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl
#print axioms never
end BB6.Agent25Raw43B1REE1RDM44
