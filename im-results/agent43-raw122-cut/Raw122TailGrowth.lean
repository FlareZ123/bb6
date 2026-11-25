import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw122TailGrowth
open BB6Coverage BB6Coverage.Agent31Pump
namespace M3905
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨5,[],[false,false,false,false,true,false,false,false,false,true,false,false,false,false,true,false,false,false,false,true]++rep [false,true,false,false,false,false,true,false,false,true,false,false,false,false,true,false,true] n⟩
theorem entry : run0 table 158 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) : run0 table 581 (family n) = some (family (n+1)) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 158 (fun _ => 581) entry (by intro n; decide) growth m hm
#print axioms never
end M3905
namespace M3906
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨5,[],[false,false,false,false,true,false,false,false,false,true]++rep [false,false,false,false,true,false,true,false,false,false,true,false,false] n⟩
theorem entry : run0 table 34 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) : run0 table 293 (family n) = some (family (n+1)) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 34 (fun _ => 293) entry (by intro n; decide) growth m hm
#print axioms never
end M3906
namespace M3908
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨5,[],[false,false,false,false,true,false,false,false,false,true]++rep [false,false,false,false,true,false,true,false,false,false,true,false,false] n⟩
theorem entry : run0 table 34 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) : run0 table 261 (family n) = some (family (n+1)) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 34 (fun _ => 261) entry (by intro n; decide) growth m hm
#print axioms never
end M3908
end BB6Coverage.Agent31Pump.Raw122TailGrowth
