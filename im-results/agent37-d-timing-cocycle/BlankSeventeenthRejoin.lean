import Lean.Elab.Tactic.Omega
import BlankSeventeenthException
import ExceptionalE7ThirdReturn
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SeventeenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def packet17Time : Nat :=
  BB6.Agent2E7ThirdReturn.totalTime u17 2

def reentry17Time : Nat := exception17Time + packet17Time

/-- The genuine blank D orbit passes the seventeenth exceptional E input,
    uses its exact three-return E/E/A source packet, and rejoins L(a,3,2). -/
theorem blank_seventeenth_reentry :
    ObsEq (run reentry17Time blank)
      (DRegularSource.sourceSection
        ⟨8 * (64 * u17 + 10) + 39, 3, 2⟩) := by
  have hstart :
      BB6.Agent2E7ThirdReturn.sourceStart u17 2 =
        DRegularSource.sourceSection ⟨9 * t17 + 7, 7, 1⟩ := by
    unfold BB6.Agent2E7ThirdReturn.sourceStart
    congr 1
  have hpacket :=
    BB6.Agent2E7ThirdReturn.exceptional_EEA_rejoin u17 2 (by omega)
  rw [hstart] at hpacket
  exact source_chain exception17Time packet17Time blank
    (DRegularSource.sourceSection ⟨9 * t17 + 7, 7, 1⟩)
    (BB6.Agent2E7ThirdReturn.sourceEnd u17 2)
    blank_seventeenth_exception
    (by simpa only [packet17Time] using hpacket)

#print axioms blank_seventeenth_reentry

end BB6.Agent2SeventeenthRoot
