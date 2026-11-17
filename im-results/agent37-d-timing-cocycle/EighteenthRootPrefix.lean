import EighteenthArithmetic
import BlankSeventeenthRejoin

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2EighteenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

/-- Lift the 2,902-step regular segment from the certified seventeenth
    blank-root reentry to the authentic eighteenth exceptional source section. -/
theorem blank_eighteenth_exception :
    ObsEq (run exception18Time blank)
      (DRegularSource.sourceSection ⟨9*t18+4,3,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent2SeventeenthRoot.reentry17Time
    2902 seed18 ⟨9*t18+4,3,1⟩
  · exact seed18_canon
  · exact terminal2902_exact
  · exact BB6.Agent2SeventeenthRoot.blank_seventeenth_reentry

#print axioms blank_eighteenth_exception

end BB6.Agent2EighteenthRoot
