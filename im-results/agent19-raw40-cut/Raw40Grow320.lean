import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.Grow320
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB1RC_1RC0RF_0RD1RE_1LD1LA_---0LF_0RC1LC
-- E0 remains free.
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def pre : List Bool := rep [false] 13++[true,true,true]
def block : List Bool := [false,true,true,true]
def suffix : List Bool := rep [false] 10++rep [true] 6
def family (n : Nat) : Z0 := ⟨5,[true],pre++rep block n++suffix⟩
theorem pump (R : List Bool) : run0 table 216 ⟨5,[true],pre++R⟩ = some ⟨5,[true],pre++block++R⟩ := by rfl
theorem grow (n : Nat) : run0 table 216 (family n) = some (family (n+1)) := by
  simpa only [family,rep,List.append_assoc] using pump (rep block n++suffix)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1170 (fun _ => 216) (by rfl) (by omega) grow m hm
#print axioms never
end BB6.Agent19Raw40.Grow320
