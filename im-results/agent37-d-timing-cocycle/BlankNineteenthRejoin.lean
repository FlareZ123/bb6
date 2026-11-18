import NineteenthRootPrefix
import ExceptionalAGeneral

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2NineteenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def packet19Time : Nat :=
  BB6.Agent32EAll.duration (3*t19+2) 8 +
    BB6.Agent25AGeneral.aCost t19 2

def reentry19Time : Nat := exception19Time+packet19Time

/-- The original-source E/A packet returns the nineteenth exception to
    a pure-unary regular section. -/
theorem blank_nineteenth_reentry :
    ObsEq (run reentry19Time blank)
      (DRegularSource.sourceSection ⟨64*t19+113,0,0⟩) := by
  exact source_chain exception19Time packet19Time blank
    (DRegularSource.sourceSection ⟨9*t19+10,9,1⟩)
    (DRegularSource.sourceSection ⟨64*t19+113,0,0⟩)
    blank_nineteenth_exception
    (by simpa only [packet19Time] using
      (BB6.Agent25AGeneral.exceptional_EA_general t19 2))

#print axioms blank_nineteenth_reentry

end BB6.Agent2NineteenthRoot
