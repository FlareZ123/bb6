import Lean.Elab.Tactic.Omega
import BlankSeventeenthRejoin
import ExceptionalBGeneral

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2EighteenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def seed18 : DRegular.L :=
  ⟨8*(64*BB6.Agent2SeventeenthRoot.u17+10)+39,3,2⟩

def terminal2902 : DRegular.L :=
  (DRegular.run 2902 seed18).getD ⟨9,0,0⟩

def t18 : Nat := (terminal2902.a-4)/9

/-- Exact DRegular state and residue after the proposed seventeenth E/E/A reentry. -/
theorem terminal2902_certificate :
    DRegular.run 2902 seed18 = some ⟨9*t18+4,3,1⟩ ∧
      t18 % 27 = 22 := by decide

theorem terminal2902_exact :
    DRegular.run 2902 seed18 = some ⟨9*t18+4,3,1⟩ :=
  terminal2902_certificate.1

theorem t18_mod27 : t18 % 27 = 22 :=
  terminal2902_certificate.2

def exception18Time : Nat :=
  BB6.Agent2SeventeenthRoot.reentry17Time +
    DRegular.accumulated 2902 seed18

theorem blank_eighteenth_exception :
    ObsEq (run exception18Time blank)
      (DRegularSource.sourceSection ⟨9*t18+4,3,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent2SeventeenthRoot.reentry17Time
    2902 seed18 ⟨9*t18+4,3,1⟩
  · constructor
    · change 8*(64*BB6.Agent2SeventeenthRoot.u17+10)+39 ≥ 2
      omega
    · left
      change (3:Nat) ≠ 0
      omega
  · exact terminal2902_exact
  · exact BB6.Agent2SeventeenthRoot.blank_seventeenth_reentry

def packet18Time : Nat :=
  BB6.Agent32EAll.duration (3*t18) 2 +
    BB6.Agent25BGeneral.bCost t18

def reentry18Time : Nat := exception18Time+packet18Time

theorem blank_eighteenth_reentry :
    ObsEq (run reentry18Time blank)
      (DRegularSource.sourceSection ⟨64*t18+23,1,5⟩) := by
  exact source_chain exception18Time packet18Time blank
    (DRegularSource.sourceSection ⟨9*t18+4,3,1⟩)
    (DRegularSource.sourceSection ⟨64*t18+23,1,5⟩)
    blank_eighteenth_exception
    (by simpa only [packet18Time] using
      (BB6.Agent25BGeneral.exceptional_EB_general t18 1))

#print axioms terminal2902_exact
#print axioms t18_mod27
#print axioms blank_eighteenth_exception
#print axioms blank_eighteenth_reentry

end BB6.Agent2EighteenthRoot
