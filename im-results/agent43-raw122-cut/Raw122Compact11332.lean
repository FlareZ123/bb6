import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw122DirectGrowth
open BB6Coverage BB6Coverage.Agent31Pump
namespace M11332Compact
-- 1RB0LA1RC0LB0RD0LE1LD1RE0RA0LF---1LB

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,[true,true,false,true,false,true],[false,true,false,false,false,true,false,true,true,false,true] ++ rep [true,false,true,false,false,true,false,false,false,false,false,false] n ++ [true,false,true,false,true,false,true]⟩

theorem entry : run0 table 604 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) : run0 table 554 (family n) = some (family (n+1)) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 604 (fun _ => 554) entry (by intro n; decide) growth m hm
#print axioms never
end M11332Compact
end BB6Coverage.Agent31Pump.Raw122DirectGrowth
