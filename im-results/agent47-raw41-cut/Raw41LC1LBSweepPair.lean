import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41.LC1LBPair
open BB6Coverage BB6Coverage.Agent31Pump
-- Indices 1 and 2; F1 is 0RB or 0RE, respectively. F0 is arbitrary.
def table (b : Bool) : PartialMachine := fun s =>
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
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨false,true,if b then 4 else 1⟩)
  | _,_ => none

def P : List Bool := [true,false,true,true]
def V : List Bool := [false,false,true,false]
def family (n : Nat) : Z0 := ⟨0,[],rep V (n+1)++[true]⟩

theorem entry (b : Bool) : run0 (table b) 10 ⟨0,[],[]⟩ = some (family 0) := by cases b <;> rfl
theorem start (b : Bool) (R : List Bool) : run0 (table b) 4 ⟨0,[],V++R⟩ = some ⟨0,[false]++P,R⟩ := by cases b <;> rfl
theorem rightOne (b : Bool) (L R : List Bool) : run0 (table b) 4 ⟨0,[false]++L,V++R⟩ = some ⟨0,[false]++P++L,R⟩ := by cases b <;> rfl
theorem turn (b : Bool) (L : List Bool) : run0 (table b) 15 ⟨0,[false]++P++L,[true]⟩ = some ⟨0,[true,true]++L,V++[true]⟩ := by cases b <;> rfl
theorem leftOne (b : Bool) (L R : List Bool) : run0 (table b) 4 ⟨0,[true,true]++P++L,R⟩ = some ⟨0,[true,true]++L,V++R⟩ := by cases b <;> rfl
theorem finish (b : Bool) (R : List Bool) : run0 (table b) 6 ⟨0,[true,true],R⟩ = some ⟨0,[],V++R⟩ := by cases b <;> rfl

theorem growth (b : Bool) (n : Nat) : run0 (table b) (8*n+25) (family n) = some (family (n+1)) := by
  have h1 := start b (rep V n++[true])
  have h2 := sweepR (table b) 0 [false] [] V P 4 (rightOne b) n P [true]
  simp only [List.nil_append,List.append_assoc,rep_snoc] at h2
  have h3 := turn b (rep P n)
  have h4 := sweepL (table b) 0 [true,true] [] P V 4 (leftOne b) n [] (V++[true])
  simp only [List.nil_append,List.append_nil] at h4
  have h5 := finish b (rep V n++V++[true])
  have h5' : run0 (table b) 6 ⟨0,[true,true],rep V n++(V++[true])⟩ = some (family (n+1)) := by
    unfold family
    change _ = some (⟨0,[],(V++rep V (n+1))++[true]⟩ : Z0)
    have e : rep V n ++ V = rep V (n+1) := rep_snoc V n
    rw [← e]
    simpa only [List.append_assoc] using h5
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5'
  rw [show 4+4*n+15+4*n+6=8*n+25 by omega] at H
  exact H

theorem never (b : Bool) (m : Machine) (hm : compatible (table b) m) : NeverHalts m :=
  never_of_growth (table b) family 10 (fun n => 8*n+25) (entry b) (by omega) (growth b) m hm
#print axioms never
end BB6.Agent47Raw41.LC1LBPair
