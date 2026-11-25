import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41.LC1LB7
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB0LC_1RC0LE_0RD1LB_1LD1RA_0LA0RF_0RE---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,0⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | _,_ => none

def P : List Bool := [false,true,false,true,true]
def V : List Bool := [false,false,true,false,true]
def family (n : Nat) : Z0 := ⟨0,[],rep V (n+1)⟩

theorem entry : run0 table 10 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem start (R : List Bool) : run0 table 4 ⟨0,[],V++R⟩ = some ⟨0,P,[true]++R⟩ := by rfl
theorem rightOne (L R : List Bool) : run0 table 9 ⟨0,P++L,[true]++V++R⟩ = some ⟨0,P++P++L,[true]++R⟩ := by rfl
theorem turn (L : List Bool) : run0 table 11 ⟨0,P++L,[true]⟩ = some ⟨0,[true,true,true]++P++L,[true]⟩ := by rfl
theorem leftOne (L R : List Bool) : run0 table 9 ⟨0,[true,true,true]++P++L,[true]++R⟩ = some ⟨0,[true,true,true]++L,[true]++V++R⟩ := by rfl
theorem finish (R : List Bool) : run0 table 4 ⟨0,[true,true,true],[true]++R⟩ = some ⟨0,[],V++R⟩ := by rfl

theorem growth (n : Nat) : run0 table (18*n+28) (family n) = some (family (n+1)) := by
  have h1 := start (rep V n)
  have h2 := sweepR table 0 P [true] V P 9 rightOne n [] []
  simp only [List.append_nil] at h2
  have h3 := turn (rep P n)
  have h4 := sweepL table 0 [true,true,true] [true] P V 9 leftOne (n+1) [] []
  simp only [List.append_nil] at h4
  have h5 := finish (rep V (n+1))
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [show 4+9*n+11+9*(n+1)+4=18*n+28 by omega] at H
  exact H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 10 (fun n => 18*n+28) entry (by omega) growth m hm
#print axioms never
end BB6.Agent47Raw41.LC1LB7
