import Raw59ReturnMachine
import MacroFARBridge

namespace BB6Coverage.Agent32Return1582

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | _,_ => none

theorem tab_eq : MacroFARBridge.project table = Raw59Return.tab := by
  funext q b
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  MacroFARBridge.never_of_live table (by rw [tab_eq]; exact Raw59Return.live) m hm

#print axioms never
end BB6Coverage.Agent32Return1582
