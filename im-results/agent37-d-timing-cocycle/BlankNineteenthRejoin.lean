import Lean.Elab.Tactic.Omega
import BlankEighteenthRejoin
import ExceptionalAGeneral

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2NineteenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def seed19 : DRegular.L :=
  ⟨64*BB6.Agent2EighteenthRoot.t18+23,1,5⟩

def terminal9780 : DRegular.L :=
  (DRegular.run 9780 seed19).getD ⟨9,0,0⟩

def t19 : Nat := (terminal9780.a-10)/9

/-- Exact DRegular state and residue after the eighteenth E/B reentry. -/
theorem terminal9780_certificate :
    DRegular.run 9780 seed19 = some ⟨9*t19+10,9,1⟩ ∧
      t19 % 27 = 12 := by decide

theorem terminal9780_exact :
    DRegular.run 9780 seed19 = some ⟨9*t19+10,9,1⟩ :=
  terminal9780_certificate.1

theorem t19_mod27 : t19 % 27 = 12 :=
  terminal9780_certificate.2

def exception19Time : Nat :=
  BB6.Agent2EighteenthRoot.reentry18Time +
    DRegular.accumulated 9780 seed19

theorem blank_nineteenth_exception :
    ObsEq (run exception19Time blank)
      (DRegularSource.sourceSection ⟨9*t19+10,9,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent2EighteenthRoot.reentry18Time
    9780 seed19 ⟨9*t19+10,9,1⟩
  · constructor
    · change 64*BB6.Agent2EighteenthRoot.t18+23 ≥ 2
      omega
    · left
      change (1:Nat) ≠ 0
      omega
  · exact terminal9780_exact
  · exact BB6.Agent2EighteenthRoot.blank_eighteenth_reentry

def packet19Time : Nat :=
  BB6.Agent32EAll.duration (3*t19+2) 8 +
    BB6.Agent25AGeneral.aCost t19 2

def reentry19Time : Nat := exception19Time+packet19Time

theorem blank_nineteenth_reentry :
    ObsEq (run reentry19Time blank)
      (DRegularSource.sourceSection ⟨64*t19+113,0,0⟩) := by
  exact source_chain exception19Time packet19Time blank
    (DRegularSource.sourceSection ⟨9*t19+10,9,1⟩)
    (DRegularSource.sourceSection ⟨64*t19+113,0,0⟩)
    blank_nineteenth_exception
    (by simpa only [packet19Time] using
      (BB6.Agent25AGeneral.exceptional_EA_general t19 2))

#print axioms terminal9780_exact
#print axioms t19_mod27
#print axioms blank_nineteenth_exception
#print axioms blank_nineteenth_reentry

end BB6.Agent2NineteenthRoot
