import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw60RFGlider
open BB6Coverage BB6Coverage.Agent31Pump
inductive V | ld | ra deriving DecidableEq

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some (match v with | .ld => ⟨true,false,3⟩ | .ra => ⟨true,true,0⟩))
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none
abbrev P : List Bool := [false,false,false,false,false,false,false,false] ++ List.replicate 18 true ++ List.replicate 11 false ++ [true,true,true]
abbrev Q : List Bool := List.replicate 10 false ++ [true,true,true]
abbrev Z : List Bool := List.replicate 17 false ++ [true,true,true]
def family (n : Nat) : Z0 := ⟨1,[],P ++ rep Q n ++ Z⟩
def entryTime : V → Nat | .ld => 1773 | .ra => 1653
def epochTime : V → Nat | .ld => 581 | .ra => 539

theorem epoch (v : V) (R : List Bool) : run0 (table v) (epochTime v) ⟨1,[],P++R⟩ = some ⟨1,[],P++Q++R⟩ := by cases v <;> rfl
theorem entry (v : V) : run0 (table v) (entryTime v) ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl
theorem growth (v : V) (n : Nat) : run0 (table v) (epochTime v) (family n) = some (family (n+1)) := by
  simpa only [family,rep,List.append_assoc] using epoch v (rep Q n++Z)
theorem positive (v : V) (_n : Nat) : 0 < epochTime v := by cases v <;> decide
theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family (entryTime v) (fun _ => epochTime v) (entry v) (positive v) (growth v) m hm

namespace M4335
abbrev table := _root_.BB6.Agent1Raw60RFGlider.table .ld
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  _root_.BB6.Agent1Raw60RFGlider.never .ld m hm
end M4335
namespace M4336
abbrev table := _root_.BB6.Agent1Raw60RFGlider.table .ra
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  _root_.BB6.Agent1Raw60RFGlider.never .ra m hm
end M4336

#print axioms epoch
#print axioms growth
#print axioms never
end BB6.Agent1Raw60RFGlider
