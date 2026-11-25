import BlockFARBridge
import Q02700Proof

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent5Q0HeldBlock

open BB6Coverage

/-- Literal primitive table represented by the offset-2700 q0 held leaf.
    D0 is the unique unassigned transition. -/
def q2700Entries : List (Option BB6BlockFAR.Move) := [
  some ⟨true, true, 1⟩,
  some ⟨false, false, 3⟩,
  some ⟨true, false, 2⟩,
  some ⟨true, true, 0⟩,
  some ⟨true, false, 4⟩,
  some ⟨true, false, 0⟩,
  none,
  some ⟨false, true, 1⟩,
  some ⟨true, true, 4⟩,
  some ⟨false, true, 5⟩,
  some ⟨true, true, 5⟩,
  some ⟨false, false, 2⟩
]

def q2700Expected : BB6BlockFAR.Table := fun q b =>
  q2700Entries[2 * q.val + b.toNat]?.getD none

theorem q2700_generated_table_exact :
    BB6BlockFAR.Q02700.machine = q2700Expected := by
  rfl

def q0_2700 : PartialMachine :=
  BB6BlockFAR.partialTable BB6BlockFAR.Q02700.machine

theorem q0_2700_never (m : Machine)
    (hm : compatible q0_2700 m) : NeverHalts m :=
  BB6BlockFAR.transfer_never BB6BlockFAR.Q02700.machine m hm
    BB6BlockFAR.Q02700.never

theorem q0_2700_parent_slots :
    q0_2700 (⟨0, by decide⟩, false) =
        some (some ⟨true, true, 1⟩) ∧
    q0_2700 (⟨1, by decide⟩, false) =
        some (some ⟨true, false, 2⟩) := by
  decide

theorem q0_2700_D0_is_the_only_hole :
    q0_2700 (⟨3, by decide⟩, false) = none := by
  decide

#print axioms q2700_generated_table_exact
#print axioms q0_2700_never
#print axioms q0_2700_parent_slots
#print axioms q0_2700_D0_is_the_only_hole

end BB6.Agent5Q0HeldBlock
