import SweepPumping

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent19Raw40
open BB6Coverage BB6Coverage.Agent31Pump

-- 1RB0LA_1RC---_0RD0RC_1LD1LA_------_------
def pumpTable : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨2,[true,true,true],rep [true] (3*n+2)⟩

theorem entry : run0 pumpTable 9 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem rightOne (L R : List Bool) :
    run0 pumpTable 1 ⟨2,[true]++L,[true]++R⟩ =
      some ⟨2,[true]++[false]++L,R⟩ := by rfl

theorem rightSweep (k : Nat) :
    run0 pumpTable k ⟨2,[true,true,true],rep [true] k⟩ =
      some ⟨2,[true]++rep [false] k++[true,true],[]⟩ := by
  simpa using sweepR pumpTable 2 [true] [] [true] [false] 1 rightOne k [true,true] []

theorem turnaround (k : Nat) :
    run0 pumpTable 2 ⟨2,[true]++rep [false] k++[true,true],[]⟩ =
      some ⟨3,rep [false] (k+3)++[true,true],[]⟩ := by
  rfl

theorem leftOne (L R : List Bool) :
    run0 pumpTable 1 ⟨3,[false]++L,R⟩ = some ⟨3,L,[true]++R⟩ := by rfl

theorem leftSweep (k : Nat) :
    run0 pumpTable k ⟨3,rep [false] k++[true,true],[]⟩ =
      some ⟨3,[true,true],rep [true] k⟩ := by
  simpa using sweepL pumpTable 3 [] [] [false] [true] 1 leftOne k [true,true] []

theorem restart (k : Nat) :
    run0 pumpTable 4 ⟨3,[true,true],rep [true] (k+3)⟩ =
      some ⟨2,[true,true,true],rep [true] (k+3)⟩ := by rfl

theorem growth (n : Nat) : run0 pumpTable (6*n+13) (family n) = some (family (n+1)) := by
  let k := 3*n+2
  have H := join0 (join0 (join0 (rightSweep k) (turnaround k)) (leftSweep (k+3))) (restart k)
  have ht : k+2+(k+3)+4 = 6*n+13 := by dsimp [k]; omega
  have hn : k+3 = 3*(n+1)+2 := by dsimp [k]; omega
  rw [ht,hn] at H
  exact H

theorem pump_never (m : Machine) (hm : compatible pumpTable m) : NeverHalts m :=
  never_of_growth pumpTable family 9 (fun n => 6*n+13) entry (by omega) growth m hm

#print axioms pump_never
end BB6.Agent19Raw40
