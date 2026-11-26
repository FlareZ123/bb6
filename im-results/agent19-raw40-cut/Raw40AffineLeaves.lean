import Raw40AffineCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.AffineLeaves
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent19Raw40.NestedCore
namespace Leaf1240
-- 1RB1RC1RC1RE0RD0RC1LD1LA1RF0LE1RB---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem core : Core table := by constructor <;> rfl

theorem prep (R : List Bool) : run0 table 36 ⟨1,[true,true],[true,true,true]++R⟩ =
      some ⟨2,[true,true],[true,true,true,true,true]++R⟩ := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  AffineCore.never table core prep 18 2 (by rfl) m hm
#print axioms never
end Leaf1240
namespace Leaf1259
-- 1RB1RC1RC1RE0RD0RC1LD1LA---0LF1RA0LF
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

theorem core : Core table := by constructor <;> rfl

theorem prep (R : List Bool) : run0 table 36 ⟨1,[true,true],[true,true,true]++R⟩ =
      some ⟨2,[true,true],[true,true,true,true,true]++R⟩ := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  AffineCore.never table core prep 18 2 (by rfl) m hm
#print axioms never
end Leaf1259
end BB6.Agent19Raw40.AffineLeaves
