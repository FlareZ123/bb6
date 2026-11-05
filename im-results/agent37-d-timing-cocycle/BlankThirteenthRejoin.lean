import Lean.Elab.Tactic.Omega
import BlankTwelfthRejoin

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent37ThirteenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def seed13 : DRegular.L :=
  ⟨64*BB6.Agent37TwelfthRoot.t12+91,3,2⟩

def terminal3679 : DRegular.L :=
  (DRegular.run 3679 seed13).getD ⟨9,0,0⟩

def t13 : Nat := (terminal3679.a-4)/9

/-- Exact computation in the original-source-certified DRegular model:
    3679 regular sections after the twelfth true-root reentry, the
    thirteenth exceptional source has six alternating pairs. -/
theorem terminal3679_exact :
    DRegular.run 3679 seed13 = some ⟨9*t13+4,6,1⟩ := by decide

def exception13Time : Nat :=
  BB6.Agent37TwelfthRoot.reentry12Time +
    DRegular.accumulated 3679 seed13

/-- Actual blank-origin source transport, not merely a synthetic E input. -/
theorem blank_thirteenth_exception :
    ObsEq (run exception13Time blank)
      (DRegularSource.sourceSection ⟨9*t13+4,6,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent37TwelfthRoot.reentry12Time
    3679 seed13 ⟨9*t13+4,6,1⟩
  · constructor
    · change 64*BB6.Agent37TwelfthRoot.t12+91 ≥ 2
      omega
    · left
      change (3:Nat) ≠ 0
      omega
  · exact terminal3679_exact
  · exact BB6.Agent37TwelfthRoot.blank_twelfth_reentry

def packet13Time : Nat :=
  BB6.Agent32EAll.duration (3*t13) 5 +
    BB6.Agent25BGeneral.bCost t13

def reentry13Time : Nat := exception13Time+packet13Time

/-- Two original-source E/B returns from the authentic thirteenth
    exception reach a new regular configuration. -/
theorem blank_thirteenth_reentry :
    ObsEq (run reentry13Time blank)
      (DRegularSource.sourceSection ⟨64*t13+29,1,5⟩) := by
  exact source_chain exception13Time packet13Time blank
    (DRegularSource.sourceSection ⟨9*t13+4,6,1⟩)
    (DRegularSource.sourceSection ⟨64*t13+29,1,5⟩)
    blank_thirteenth_exception
    (by simpa only [packet13Time] using
      (BB6.Agent25BGeneral.exceptional_EB_general t13 4))

#print axioms terminal3679_exact
#print axioms blank_thirteenth_exception
#print axioms blank_thirteenth_reentry

end BB6.Agent37ThirteenthRoot
