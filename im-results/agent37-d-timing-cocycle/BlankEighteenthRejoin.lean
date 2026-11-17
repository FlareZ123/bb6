import EighteenthRootPrefix
import BlankSeventeenthRejoin
import ExceptionalBGeneral

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2EighteenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def packet18Time : Nat :=
  BB6.Agent32EAll.duration (3*t18) 2 +
    BB6.Agent25BGeneral.bCost t18

def reentry18Time : Nat := exception18Time+packet18Time

/-- The original-source E/B packet return closes the eighteenth blank-root exception. -/
theorem blank_eighteenth_reentry :
    ObsEq (run reentry18Time blank)
      (DRegularSource.sourceSection ⟨64*t18+23,1,5⟩) := by
  exact source_chain exception18Time packet18Time blank
    (DRegularSource.sourceSection ⟨9*t18+4,3,1⟩)
    (DRegularSource.sourceSection ⟨64*t18+23,1,5⟩)
    blank_eighteenth_exception
    (by simpa only [packet18Time] using
      (BB6.Agent25BGeneral.exceptional_EB_general t18 1))

#print axioms blank_eighteenth_reentry

end BB6.Agent2EighteenthRoot
