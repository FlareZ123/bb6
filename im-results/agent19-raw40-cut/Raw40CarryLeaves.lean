import Raw40CarryCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.CarryLeaves
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent19Raw40.CarryCore

namespace Leaf190
-- 1RB1RC1RC1RB0RD1RE1LD1LA0RF0LE0RB---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | _,_ => none
def S : List Bool := [false,true,true,true,true,true,true,false,false]
theorem core : Core table 5 2 19 5 5 17 S := by constructor <;> intros <;> rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  CarryCore.never table 5 2 19 5 5 17 S core 89 (by rfl) m hm
#print axioms never
end Leaf190

namespace Leaf197
-- 1RB1RC1RC1RF0RD1RE1LD1LA0RF0LE1RA---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | _,_ => none
def S : List Bool := [false,true,true,true,true,false]
theorem core : Core table 3 4 9 7 5 9 S := by constructor <;> intros <;> rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  CarryCore.never table 3 4 9 7 5 9 S core 46 (by rfl) m hm
#print axioms never
end Leaf197
end BB6.Agent19Raw40.CarryLeaves
