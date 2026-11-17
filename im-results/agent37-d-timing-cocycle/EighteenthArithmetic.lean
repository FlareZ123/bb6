import Lean.Elab.Tactic.Omega
import DRegularFast
import SeventeenthSecondHalf
import BlankSeventeenthRejoin

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2EighteenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

/-- The seventeenth E/E/A return parameter is t17/3; it is defined by the
    seventeenth arithmetic certificate, not in the root-rejoin namespace. -/
def u17 : Nat := BB6.Agent2SeventeenthArithmetic.t17 / 3

def seed18 : DRegular.L :=
  ⟨8*(64*u17+10)+39,3,2⟩

theorem seed18_canon : DRegular.Canon seed18 := by
  constructor
  · dsimp [seed18, u17]
    omega
  · simp [seed18, u17]

def terminal2902 : DRegular.L :=
  (DRegular.run 2902 seed18).getD ⟨9,0,0⟩

def t18 : Nat := (terminal2902.a-4)/9

/-- Exact DRegular state and residue after the proposed seventeenth E/E/A reentry. -/
theorem terminal2902_certificate :
    DRegular.run 2902 seed18 = some ⟨9*t18+4,3,1⟩ ∧
      t18 % 27 = 22 := by
  rw [BB6.Agent2Fast64.fastRun_correct 2902 seed18 seed18_canon]
  decide

theorem terminal2902_exact :
    DRegular.run 2902 seed18 = some ⟨9*t18+4,3,1⟩ :=
  terminal2902_certificate.1

theorem t18_mod27 : t18 % 27 = 22 :=
  terminal2902_certificate.2

def exception18Time : Nat :=
  BB6.Agent2SeventeenthRoot.reentry17Time +
    DRegular.accumulated 2902 seed18

#print axioms seed18_canon
#print axioms terminal2902_certificate
#print axioms terminal2902_exact
#print axioms t18_mod27

end BB6.Agent2EighteenthRoot
