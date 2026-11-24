import FiveSlotLeafGraft
import FiniteLassoOracle

namespace BB6Coverage

/-- E/0 = 0LD: write blank, move left, enter D. -/
def agent48P4ZeroLDAction : Transition :=
  some ⟨false, false, 3⟩

/-- The existing P4 prefix with its fifth queried slot E/0 fixed to 0LD. -/
def agent48P4ZeroLD : PartialMachine :=
  refine agent27P4 agent27E0 agent48P4ZeroLDAction

/--
The blank run reaches the exact same finite configuration at steps 4 and 6.
The only rules used are the four P4 rules and E/0 = 0LD.
-/
theorem agent48P4ZeroLD_check :
    finiteLassoCheck agent48P4ZeroLD 6 = true := by
  decide

/-- Every completion of this five-slot child is nonhalting. -/
theorem agent48P4ZeroLD_cover :
    Cover (DecidedBelow 6) agent48P4ZeroLD :=
  finiteLassoCheck_sound agent48P4ZeroLD 6 agent48P4ZeroLD_check

#print axioms agent48P4ZeroLD_cover

end BB6Coverage
