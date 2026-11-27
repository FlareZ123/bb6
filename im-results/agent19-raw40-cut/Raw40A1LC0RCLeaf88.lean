import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.A1LC0RC.Leaf88
open BB6Coverage BB6Coverage.Agent31Pump
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | _,_ => none
abbrev pre : List Bool := [true,true,true,true,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,false,false]
abbrev period : List Bool := [true,true,true,true,false,false,false,false]
abbrev tail7 : List Bool := [true,true,true,true,true,true,true]
def family (n : Nat) : Z0 := ⟨0,[],pre++rep period n++tail7⟩
theorem entry : run0 table 563 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem pump (R : List Bool) : run0 table 288 ⟨0,[],pre++R⟩ =
    some ⟨0,[],pre++period++R⟩ := by rfl
theorem epoch (n : Nat) : run0 table 288 (family n) = some (family (n+1)) := by
  simpa only [family,rep,List.append_assoc] using pump (rep period n++tail7)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 563 (fun _ => 288) entry (by intro n; decide) epoch m hm
#print axioms never
end BB6.Agent19Raw40.A1LC0RC.Leaf88
