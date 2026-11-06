import Lean.Elab.Tactic.Omega
import BlankThirteenthRejoin

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2FourteenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

/-- The regular model starts from the authenticated thirteenth reentry. -/
def seed14 : DRegular.L :=
  ⟨64*BB6.Agent37ThirteenthRoot.t13+29,1,5⟩

def terminal5169 : DRegular.L :=
  (DRegular.run 5169 seed14).getD ⟨9,0,0⟩

def t14 : Nat := (terminal5169.a-4)/9

/-- Exact computation in the original-source-certified DRegular model:
    5169 regular sections after the thirteenth true-root reentry, the
    fourteenth exceptional source has five alternating pairs. -/
theorem terminal5169_exact :
    DRegular.run 5169 seed14 = some ⟨9*t14+4,5,1⟩ := by decide

def exception14Time : Nat :=
  BB6.Agent37ThirteenthRoot.reentry13Time +
    DRegular.accumulated 5169 seed14

/-- Original-source transport from the actual blank root to the fourteenth
    exceptional E/B input. -/
theorem blank_fourteenth_exception :
    ObsEq (run exception14Time blank)
      (DRegularSource.sourceSection ⟨9*t14+4,5,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent37ThirteenthRoot.reentry13Time
    5169 seed14 ⟨9*t14+4,5,1⟩
  · constructor
    · change 64*BB6.Agent37ThirteenthRoot.t13+29 ≥ 2
      omega
    · left
      change (1:Nat) ≠ 0
      omega
  · exact terminal5169_exact
  · exact BB6.Agent37ThirteenthRoot.blank_thirteenth_reentry

def packet14Time : Nat :=
  BB6.Agent32EAll.duration (3*t14) 4 +
    BB6.Agent25BGeneral.bCost t14

def reentry14Time : Nat := exception14Time+packet14Time

/-- The fourteenth authentic E exception uses the universal E/B source
    return and rejoins the original-source regular language. -/
theorem blank_fourteenth_reentry :
    ObsEq (run reentry14Time blank)
      (DRegularSource.sourceSection ⟨64*t14+27,1,5⟩) := by
  exact source_chain exception14Time packet14Time blank
    (DRegularSource.sourceSection ⟨9*t14+4,5,1⟩)
    (DRegularSource.sourceSection ⟨64*t14+27,1,5⟩)
    blank_fourteenth_exception
    (by simpa only [packet14Time] using
      (BB6.Agent25BGeneral.exceptional_EB_general t14 3))

#print axioms terminal5169_exact
#print axioms blank_fourteenth_exception
#print axioms blank_fourteenth_reentry

end BB6.Agent2FourteenthRoot
