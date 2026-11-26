import Agent46AutoPump

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent46Drift1046
open BB6Coverage Agent31Pump

def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨false,true,3⟩)
  | _,_ => none

def frame (n : Nat) : Z0 := ⟨3,[],rep [true] (n+104)⟩
theorem first : run0 p 3212 ⟨0,[],[]⟩ = some (frame 0) := by decide
theorem growth (n : Nat) : run0 p 1 (frame n) = some (frame (n+1)) := by
  rfl
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_growth p frame 3212 (fun _ => 1) first (by intro; decide) growth m hm
#print axioms never
end BB6Coverage.Agent46Drift1046
