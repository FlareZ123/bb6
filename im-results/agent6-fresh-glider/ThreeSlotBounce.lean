import EntryMacroLeft
import MacroOracle

namespace BB6Coverage

/-- A three-slot turning bootstrap. First A paints a marker and moves
    into b; b returns to A's marked cell without writing; A/1 turns
    into a virgin ray on the other side. From state b the resulting
    four-step macro repeats forever with displacement two. -/
def threeSlotBounce (right : Bool) (b : Fin 6) (y : Bool) :
    PartialMachine := fun slot =>
  if slot = (0,false) then some (some ⟨true,right,b⟩)
  else if slot = (b,false) then some (some ⟨false,!right,0⟩)
  else if slot = (0,true) then some (some ⟨y,!right,b⟩)
  else none

def rightBootstrapFamily : List PartialMachine :=
  (List.finRange 6).flatMap (fun b =>
    if b = 0 then [] else
      [threeSlotBounce true b false, threeSlotBounce true b true])

def leftBootstrapFamily : List PartialMachine :=
  (List.finRange 6).flatMap (fun b =>
    if b = 0 then [] else
      [threeSlotBounce false b false, threeSlotBounce false b true])

theorem right_bootstrap_count : rightBootstrapFamily.length = 10 := by decide
theorem left_bootstrap_count : leftBootstrapFamily.length = 10 := by decide

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- The A/0 rightward bootstrap enters a left-moving b macro after three
    steps. Every resulting sparse table has a finite certificate. -/
theorem right_bootstrap_all :
    rightBootstrapFamily.all
      (fun p => finiteEntryMacroLeftCheck p 3 4) = true := by decide

theorem left_bootstrap_all :
    leftBootstrapFamily.all
      (fun p => finiteEntryMacroCheck p 3 4) = true := by decide

theorem right_bootstrap_sound (p : PartialMachine) (bound : Nat)
    (hp : p ∈ rightBootstrapFamily) : Cover (DecidedBelow bound) p := by
  have h : finiteEntryMacroLeftCheck p 3 4 = true :=
    (List.all_eq_true.mp right_bootstrap_all) p hp
  exact finiteEntryMacroLeftCheck_sound p 3 4 bound (by decide) h

theorem left_bootstrap_sound (p : PartialMachine) (bound : Nat)
    (hp : p ∈ leftBootstrapFamily) : Cover (DecidedBelow bound) p := by
  have h : finiteEntryMacroCheck p 3 4 = true :=
    (List.all_eq_true.mp left_bootstrap_all) p hp
  exact finiteEntryMacroCheck_sound p 3 4 bound (by decide) h

/-- One fixed three-slot example is strictly outside the original A-only
    finite macro check with length cutoff four. -/
theorem right_bootstrap_b1_leaf :
    Cover (DecidedBelow 2) (threeSlotBounce true 1 false) := by
  apply finiteEntryMacroLeftCheck_sound (threeSlotBounce true 1 false) 3 4 2
    (by decide)
  decide

theorem right_bootstrap_b1_old_reject :
    finiteMacroOracle (threeSlotBounce true 1 false) 4 = false := by decide

#print axioms right_bootstrap_sound
#print axioms left_bootstrap_sound
#print axioms right_bootstrap_b1_leaf

end BB6Coverage
