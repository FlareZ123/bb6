import ZipThreeHoleAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw44Top
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent10ZipAudit BB6.Agent31ThreeHole BB6Coverage.Agent10ZipAudit

def parent : PartialMachine := fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,false,1⟩)
  | _, _ => none

def slot : Slot := (1,true)
def child (t : Transition) : PartialMachine := refine parent slot t

theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_hole : parent slot = none := by decide

#eval zipRead parent 6
#eval possibleDelays (child none) 0

theorem halt_checked : zipQueryOK 9 parent 6 slot = true := by decide +kernel

theorem halt_bound (m : Machine) (hm : compatible (child none) m) : WeightedBound 9 m := by
  obtain ⟨hread, hhole, hw⟩ := zipQueryOK_sound halt_checked
  cases hr : knownRun parent 6 with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = slot := by simpa [hr] using hread
    exact first_hole_weighted_halt 9 parent 6 c parent_root hr
      (by simpa [hs] using hhole)
      (by simpa [hs] using BB6.Agent50TNFPilot.weightOK_sound parent slot 6 9 hw)
      m (by simpa [child,hs] using hm)

theorem B1RB_never (m : Machine) (hm : compatible (child (some ⟨true,true,1⟩)) m) : NeverHalts m :=
  zipCycle_sound (child (some ⟨true,true,1⟩)) 1 9 true (0) (by decide) (by decide +kernel) m hm

theorem B1RB_bound (B : Nat) (m : Machine) (hm : compatible (child (some ⟨true,true,1⟩)) m) : WeightedBound B m :=
  weighted_never B m (B1RB_never m hm)
#print axioms B1RB_never
theorem B0LC_never (m : Machine) (hm : compatible (child (some ⟨false,false,2⟩)) m) : NeverHalts m :=
  zipCycle_sound (child (some ⟨false,false,2⟩)) 8 1 false (0) (by decide) (by decide +kernel) m hm

theorem B0LC_bound (B : Nat) (m : Machine) (hm : compatible (child (some ⟨false,false,2⟩)) m) : WeightedBound B m :=
  weighted_never B m (B0LC_never m hm)
#print axioms B0LC_never
theorem B0LD_never (m : Machine) (hm : compatible (child (some ⟨false,false,3⟩)) m) : NeverHalts m :=
  zipCycle_sound (child (some ⟨false,false,3⟩)) 7 1 false (-1) (by decide) (by decide +kernel) m hm

theorem B0LD_bound (B : Nat) (m : Machine) (hm : compatible (child (some ⟨false,false,3⟩)) m) : WeightedBound B m :=
  weighted_never B m (B0LD_never m hm)
#print axioms B0LD_never
theorem B1LD_never (m : Machine) (hm : compatible (child (some ⟨true,false,3⟩)) m) : NeverHalts m :=
  zipCycle_sound (child (some ⟨true,false,3⟩)) 7 1 false (-1) (by decide) (by decide +kernel) m hm

theorem B1LD_bound (B : Nat) (m : Machine) (hm : compatible (child (some ⟨true,false,3⟩)) m) : WeightedBound B m :=
  weighted_never B m (B1LD_never m hm)
#print axioms B1LD_never
theorem B1RD_never (m : Machine) (hm : compatible (child (some ⟨true,true,3⟩)) m) : NeverHalts m :=
  zipCycle_sound (child (some ⟨true,true,3⟩)) 5 2 true (0) (by decide) (by decide +kernel) m hm

theorem B1RD_bound (B : Nat) (m : Machine) (hm : compatible (child (some ⟨true,true,3⟩)) m) : WeightedBound B m :=
  weighted_never B m (B1RD_never m hm)
#print axioms B1RD_never
#print axioms halt_bound
end BB6.Agent16Raw44Top
