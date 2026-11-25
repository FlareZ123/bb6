import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41.LB0LC34
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB0LB_1RC0LC_0RD0RE_1LD1RA_1LB1RF_0RC---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | _,_ => none

def P : List Bool := [true,false,false]
def Q : List Bool := [false,false,true]
def Rb : List Bool := [false,true,true]
def S : List Bool := [true,true,false]
def family (n : Nat) : Z0 := ⟨4,rep P (n+1)++[true,false,true,true],[]⟩
theorem entry : run0 table 40 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem start (L : List Bool) : run0 table 9 ⟨4,P++L,[]⟩ = some ⟨2,[false,false]++L,[false,false,true,true]⟩ := by rfl

theorem leftOne (L R : List Bool) :
    run0 table 7 ⟨2,[false,false]++P++L,[false,false]++R⟩ =
      some ⟨2,[false,false]++L,[false,false]++S++R⟩ := by rfl

theorem turn (R : List Bool) :
    run0 table 20 ⟨2,[false,false,true,false,true,true],[false,false,true]++R⟩ =
      some ⟨4,[true,false,true,true],[false,true,true,false,true]++R⟩ := by rfl

theorem rightOne (L R : List Bool) :
    run0 table 3 ⟨4,[true]++L,Rb++R⟩ = some ⟨4,[true]++Q++L,R⟩ := by rfl

theorem turnWord (n : Nat) : rep S n++[true,true] = [true,true]++rep Rb n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,List.append_assoc,ih]
    rfl

theorem growth (n : Nat) : run0 table (10*n+35) (family n) = some (family (n+1)) := by
  have h1 := start (rep P n++[true,false,true,true])
  have h2 := sweepL table 2 [false,false] [false,false] P S 7 leftOne n [true,false,true,true] [true,true]
  simp only [List.append_assoc] at h2
  have h3 := turn ([true]++rep Rb n)
  have h3' : run0 table 20 ⟨2,[false,false,true,false,true,true],[false,false]++(rep S n++[true,true])⟩ =
      some ⟨4,[true,false,true,true],rep Rb (n+2)⟩ := by
    rw [turnWord]
    exact h3
  have h4 := sweepR table 4 [true] [] Rb Q 3 rightOne (n+2) [false,true,true] []
  simp only [List.append_nil,List.nil_append] at h4
  have eq : [true]++rep Q (n+2)++[false,true,true] = rep P (n+2)++[true,false,true,true] := by
    have H := rotate true [false,false] (n+2)
    change [true]++rep Q (n+2) = rep P (n+2)++[true] at H
    rw [H,List.append_assoc]
    rfl
  rw [eq] at h4
  have H := join0 (join0 (join0 h1 h2) h3') h4
  rw [show 9+7*n+20+3*(n+2)=10*n+35 by omega] at H
  exact H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 40 (fun n => 10*n+35) entry (by omega) growth m hm
#print axioms never
end BB6.Agent47Raw41.LB0LC34
