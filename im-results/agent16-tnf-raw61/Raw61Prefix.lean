import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Raw61Prefix
open BB6Coverage Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | _,_ => none
abbrev P : List Bool := [false,false,true,false,true,false,true,false,false,false,true,false,false,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,true,false,false,false,true,false,true,false,true,false,false,false,false,false,true,false,false,true,false,false,false,false,false,false]
abbrev I : List Bool := [false,false,false,false,false,true,false,true,false,false,false,true]
abbrev R0 : List Bool := [false,false,false,false,false,true,false,true,false,false,false,true,false,true,false,true,false,true,false,true,false,false,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,true,false,false,false,true,false,true,false,false,false,true]
def family (n : Nat) : Z0 := ⟨0,[],P ++ rep I n ++ R0⟩
theorem entry : run0 table 10750 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem insert (R : List Bool) : run0 table 1134 ⟨0,[],P ++ R⟩ = some ⟨0,[],P ++ I ++ R⟩ := by rfl
theorem growth (n : Nat) : run0 table 1134 (family n) = some (family (n+1)) := by
  simpa only [family,rep,List.append_assoc] using insert (rep I n ++ R0)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 10750 (fun _ => 1134) entry (by intro n; decide) growth m hm
#print axioms entry
#print axioms insert
#print axioms growth
#print axioms never
end BB6Coverage.Raw61Prefix

namespace BB6.Agent10Recursive.R61M14
open BB6Coverage
abbrev table := Raw61Prefix.table
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Raw61Prefix.never m hm
end BB6.Agent10Recursive.R61M14
