import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41.LC0RA2
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB0LC_1RC0LE_0RD0RA_1LD1RA_0LF1LE_---0LA
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def P : List Bool := [true,false,true,true]
def Q : List Bool := [false,false,false,true]
def Rb : List Bool := [false,false,true,false]
def family (n : Nat) : Z0 := ⟨4,[true,false,true]++rep P n,[false]⟩
theorem entry : run0 table 10 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem leftOne (L R : List Bool) :
    run0 table 12 ⟨4,[true,false,true]++P++L,R⟩ =
      some ⟨4,[true,false,true]++L,Q++R⟩ := by rfl

theorem turn (R : List Bool) :
    run0 table 3 ⟨4,[true,false,true],R⟩ = some ⟨0,[],[false,false,true]++R⟩ := by rfl

theorem firstRight (R : List Bool) :
    run0 table 4 ⟨0,[],Rb++R⟩ = some ⟨0,[false]++P,R⟩ := by rfl

theorem rightOne (L R : List Bool) :
    run0 table 4 ⟨0,[false]++L,Rb++R⟩ = some ⟨0,[false]++P++L,R⟩ := by rfl

theorem finish (L : List Bool) :
    run0 table 10 ⟨0,[false]++P++L,[]⟩ = some ⟨4,[true,false,true]++P++L,[false]⟩ := by rfl

theorem rotateRight (n : Nat) : [false,false,true]++rep Q n++[false] = Rb++rep Rb n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Rb++([false,false,true]++rep Q n++[false]) = Rb++(Rb++rep Rb n)
    rw [ih]

theorem growth (n : Nat) : run0 table (16*n+17) (family n) = some (family (n+1)) := by
  have h1 := sweepL table 4 [true,false,true] [] P Q 12 leftOne n [] [false]
  simp only [List.append_nil,List.nil_append] at h1
  have h2 := turn (rep Q n++[false])
  have h2' : run0 table 3 ⟨4,[true,false,true],rep Q n++[false]⟩ =
      some ⟨0,[],Rb++rep Rb n⟩ := by
    rw [← rotateRight]
    simpa only [List.append_assoc] using h2
  have h3 := firstRight (rep Rb n)
  have h4 := sweepR table 0 [false] [] Rb P 4 rightOne n P []
  simp only [List.append_nil,List.nil_append] at h4
  have h5 := finish (rep P n)
  have h5' : run0 table 10 ⟨0,[false]++rep P n++P,[]⟩ = some (family (n+1)) := by
    rw [List.append_assoc,rep_snoc]
    exact h5
  have H := join0 (join0 (join0 (join0 h1 h2') h3) h4) h5'
  rw [show 12*n+3+4+4*n+10=16*n+17 by omega] at H
  exact H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 10 (fun n => 16*n+17) entry (by omega) growth m hm
#print axioms never
end BB6.Agent47Raw41.LC0RA2
