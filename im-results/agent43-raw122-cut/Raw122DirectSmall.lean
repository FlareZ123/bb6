import SweepPumping

set_option maxRecDepth 100000

set_option maxHeartbeats 0

namespace BB6Coverage.Agent31Pump.Raw122DirectGrowth

open BB6Coverage BB6Coverage.Agent31Pump

namespace M28

-- 1RB0RC_1RC---_0RD0LE_1LD1RE_1RA0LF_1RB0LC

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

def family (n : Nat) : Z0 := ⟨3,[true,false,true,true,true,true,false,true,true,true],[false,false,false,true] ++ rep [false,false,false,false,true,false,true,false,false,false,true,false,false] n⟩

theorem entry : run0 table 94 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table 293 (family n) = some (family (n+1)) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 94 (fun _ => 293) entry (by intro n; decide) growth m hm

#print axioms never

end M28

namespace M29

-- 1RB1LD_1RC---_0RD0LE_1LD1RE_1RA0LF_1RB0LC

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

def family (n : Nat) : Z0 := ⟨3,[true,false,true,true,true,true,false,true,true,true],[false,false,false,true] ++ rep [false,false,false,false,true,false,true,false,false,false,true,false,false] n⟩

theorem entry : run0 table 86 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table 261 (family n) = some (family (n+1)) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 86 (fun _ => 261) entry (by intro n; decide) growth m hm

#print axioms never

end M29

namespace M32

-- 1RB---_1RC0RB_0RD0RE_1LD1RE_1RA0LF_1LB0LE

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[false,true,false,true] ++ rep [true,false,true,true,true,false,true,false,true,true,true,false,true,true,false,true,true,true,false,false,true,true,false,true,true,true,false,true,true,false] n,[false,true]⟩

theorem entry : run0 table 13 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table 346 (family n) = some (family (n+1)) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 13 (fun _ => 346) entry (by intro n; decide) growth m hm

#print axioms never

end M32

end BB6Coverage.Agent31Pump.Raw122DirectGrowth
