import Lean.Elab.Tactic.Omega
import BlankEleventhRejoin
import TwelfthPacket

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent37TwelfthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def seed12 : DRegular.L :=
  ⟨32768*(BB6.Agent25EleventhRoot.t11/27)+5493,0,0⟩

def terminal1759 : DRegular.L :=
  (DRegular.run 1759 seed12).getD ⟨9,0,0⟩

def t12 : Nat := (terminal1759.a-10)/9

/-- The actual, computed post-eleventh root is the q7 E exception,
    after exactly 1759 more defined regular-model returns. -/
theorem terminal1759_exact :
    DRegular.run 1759 seed12 = some ⟨9*t12+10,7,1⟩ := by decide

def reentry11Time : Nat :=
  BB6.Agent25EleventhRoot.eleventhExceptionTime +
    BB6.Agent25EleventhPacket.fiveCost
      (BB6.Agent25EleventhRoot.t11/27)

def exception12Time : Nat :=
  reentry11Time+DRegular.accumulated 1759 seed12

theorem blank_twelfth_exception :
    ObsEq (run exception12Time blank)
      (DRegularSource.sourceSection ⟨9*t12+10,7,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    reentry11Time 1759 seed12 ⟨9*t12+10,7,1⟩
  · constructor
    · change 32768*(BB6.Agent25EleventhRoot.t11/27)+5493 ≥ 2
      omega
    · right
      change (0:Nat)=0
      rfl
  · exact terminal1759_exact
  · exact BB6.Agent25EleventhRoot.blank_eleventh_reentry_exact

def reentry12Time : Nat :=
  exception12Time+BB6.Agent37TwelfthPacket.totalTime t12

/-- Authenticated genuine blank-root twelfth exceptional two-return
    continuation: the q=7 E and mixed A-110111 packets rejoin the
    original-source regular language L(64*t+91,3,2). -/
theorem blank_twelfth_reentry :
    ObsEq (run reentry12Time blank)
      (DRegularSource.sourceSection ⟨64*t12+91,3,2⟩) := by
  exact source_chain exception12Time
    (BB6.Agent37TwelfthPacket.totalTime t12)
    blank
    (DRegularSource.sourceSection ⟨9*t12+10,7,1⟩)
    (DRegularSource.sourceSection ⟨64*t12+91,3,2⟩)
    blank_twelfth_exception
    (BB6.Agent37TwelfthPacket.two_returns t12)

#print axioms terminal1759_exact
#print axioms blank_twelfth_exception
#print axioms blank_twelfth_reentry
end BB6.Agent37TwelfthRoot
