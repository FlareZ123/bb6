import SourceBridge192
import Agent46TerminalLifts
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0

namespace A4Backward192

/-- Companion mixed192 cylinder obtained by two forced original-source predecessors. -/
theorem source_no_131_157 (a k : Nat)
    (ha : a % 192 = 131) (hk : k % 192 = 157)
    (hr : BB6CLine.Reach (a,k,0)) : False := by
  have hlarge : 4 ≤ k := by omega
  have hp : BB6CLine.Reach (a,k-3,3) :=
    BB6.Agent46.reach_c0_two_parent a k hlarge hr
  have hnever := source_blank_never_bad192 (a,k-3,3) hp
  apply hnever
  simp only [bad,show ¬((3:Nat)<2) by omega,↓reduceIte,high]
  right;right;right;right;left
  constructor
  · omega
  · right
    omega

#print axioms source_no_131_157
end A4Backward192
