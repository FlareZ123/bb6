import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B1REE1LCM41
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,2⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | _,_ => none

def P : Nat → List Bool
  | 0 => [false,true,false,false]
  | n+1 => true::false::P n

def ones (n : Nat) := List.replicate n true

def A0 (n : Nat) : Z0 := ⟨0,false::false::P (2*n+1),[]⟩
def A1 (j : Nat) (R : List Bool) : Z0 := ⟨0,P (2*j+2),R⟩
def C (n : Nat) (R : List Bool) : Z0 := ⟨2,P n,R⟩

theorem sweep (n : Nat) (R : List Bool) :
    run0 table (2*n) (C n R) = some (C 0 (ones (2*n)++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 2 (C (n+1) R) = some (C n (true::true::R)) := by rfl
    have H := join0 h (ih (true::true::R))
    have he : ones (2*n) ++ true::true::R = ones (2*(n+1)) ++ R := by
      have h' : 2*(n+1)=2*n+2 := by omega
      rw [h']
      simp only [ones,← List.replicate_append_replicate,List.append_assoc]
      rfl
    rw [he] at H
    simpa only [show 2+2*n=2*(n+1) by omega] using H

theorem finish (U : List Bool) :
    run0 table 10 (C 0 (true::true::true::true::U)) = some (A1 0 U) := by rfl

theorem carry (j : Nat) (U : List Bool) :
    run0 table 4 (A1 j ([true,true,false,true]++U)) = some (A1 (j+1) U) := by
  have h : 2*(j+1)+2=(2*j+2)+2 := by omega
  simp only [A1,h,P]
  rfl

theorem terminal (j : Nat) :
    run0 table 4 (A1 j [true,true,false]) = some (A0 (j+1)) := by
  have h : 2*(j+1)+1=(2*j+2)+1 := by omega
  simp only [A1,A0,h,P]
  rfl

theorem reset (j : Nat) (U : List Bool) :
    run0 table (4*j+20) (A1 j ([true,true,true,true]++U)) =
      some (A1 0 (ones (4*j+2)++[false,true]++U)) := by
  have h1 : run0 table 4 (A1 j ([true,true,true,true]++U)) =
      some (C (2*j+3) ([false,true]++U)) := by
    have h : 2*j+3=(2*j+2)+1 := by omega
    simp only [A1,C,h,P]
    rfl
  have H := join0 h1 (sweep (2*j+3) ([false,true]++U))
  have he : ones (2*(2*j+3)) ++ ([false,true]++U) =
    true::true::true::true::(ones (4*j+2)++[false,true]++U) := by
    have h : 2*(2*j+3)=4+(4*j+2) := by omega
    rw [h]
    simp only [ones,← List.replicate_append_replicate,List.append_assoc]
    rfl
  rw [he] at H
  have H' := join0 H (finish (ones (4*j+2)++[false,true]++U))
  simpa only [show 4+2*(2*j+3)+10=4*j+20 by omega] using H'

theorem init (n : Nat) :
    run0 table (4*n+24) (A0 n) = some (A1 0 (ones (4*n+2)++[false])) := by
  have h1 : run0 table 8 (A0 n) = some (C (2*n+3) [false]) := by
    have h : 2*n+3=(2*n+1)+2 := by omega
    simp only [A0,C,h,P]
    rfl
  have H := join0 h1 (sweep (2*n+3) [false])
  have he : ones (2*(2*n+3)) ++ [false] =
    true::true::true::true::(ones (4*n+2)++[false]) := by
    have h : 2*(2*n+3)=4+(4*n+2) := by omega
    rw [h]
    simp only [ones,← List.replicate_append_replicate]
    rfl
  rw [he] at H
  have H' := join0 H (finish (ones (4*n+2)++[false]))
  simpa only [show 8+2*(2*n+3)+10=4*n+24 by omega] using H'

inductive RWord : List Bool → Prop
  | endword : RWord [true,true,false]
  | zero (R : List Bool) : RWord R → RWord ([true,true,false,true]++R)
  | one (R : List Bool) : RWord R → RWord ([true,true,true,true]++R)

theorem onesWord (n : Nat) : RWord (ones (4*n+2)++[false]) := by
  induction n with
  | zero => exact RWord.endword
  | succ n ih =>
    have h : 4*(n+1)+2=4+(4*n+2) := by omega
    rw [h]
    simp only [ones,← List.replicate_append_replicate,List.append_assoc]
    simp only [ones,← List.replicate_append_replicate,List.append_assoc] at ih
    exact RWord.one _ ih

theorem resetWord (j : Nat) (R : List Bool) (h : RWord R) :
    RWord (ones (4*j+2)++[false,true]++R) := by
  induction j with
  | zero => exact RWord.zero R h
  | succ j ih =>
    have he : 4*(j+1)+2=4+(4*j+2) := by omega
    rw [he]
    simp only [ones,← List.replicate_append_replicate,List.append_assoc]
    simp only [ones,← List.replicate_append_replicate,List.append_assoc] at ih
    exact RWord.one _ ih

inductive Inv : Z0 → Prop
  | base (n : Nat) : Inv (A0 n)
  | digit (j : Nat) (R : List Bool) : RWord R → Inv (A1 j R)

theorem stepInv (z : Z0) (h : Inv z) : ∃ t z', 0<t ∧ run0 table t z=some z' ∧ Inv z' := by
  cases h with
  | base n => exact ⟨4*n+24,_,by omega,init n,Inv.digit 0 _ (onesWord n)⟩
  | digit j R h =>
    cases h with
    | endword => exact ⟨4,_,by omega,terminal j,Inv.base (j+1)⟩
    | zero R h => exact ⟨4,_,by omega,carry j R,Inv.digit (j+1) R h⟩
    | one R h => exact ⟨4*j+20,_,by omega,reset j R,Inv.digit 0 _ (resetWord j R h)⟩

theorem start : run0 table 27 ⟨0,[],[]⟩ = some (A0 0) := by rfl

theorem live (N : Nat) : ∃ t z, N≤t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ Inv z := by
  induction N with
  | zero => exact ⟨27,_,by omega,start,Inv.base 0⟩
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
end BB6.Agent25Raw43B1REE1LCM41
