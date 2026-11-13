import Lean.Elab.Tactic.Omega
import BlankTwentiethRejoin
import ExceptionalBGeneral
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000
set_option exponentiation.threshold 2048

namespace BB6.Agent2TwentyFirstRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

/-- The twentieth reentry is the authenticated seed for the next regular
    excursion. -/
def seed21 : DRegular.L :=
  ⟨8*BB6.Agent2TwentiethRejoin.k20+9,8,5⟩

/-- Exact endpoint after 12,588 DRegular sections from the twentieth reentry. -/
def terminal12588 : DRegular.L :=
  (BB6.DRegularFast.fastRun 12588 seed21).getD ⟨9,0,0⟩

def t21 : Nat := (terminal12588.a-4)/9

theorem terminal12588_certificate :
    DRegular.run 12588 seed21 = some ⟨9*t21+4,8,1⟩ ∧
      t21 % 27 = 6 := by
  have hcanon : DRegular.Canon seed21 := by
    constructor
    · dsimp [seed21]
      omega
    · simp [seed21]
  rw [BB6.DRegularFast.fastRun_correct 12588 seed21 hcanon]
  decide

theorem terminal12588_exact :
    DRegular.run 12588 seed21 = some ⟨9*t21+4,8,1⟩ :=
  terminal12588_certificate.1

theorem t21_mod27 : t21 % 27 = 6 :=
  terminal12588_certificate.2

def exception21Time : Nat :=
  BB6.Agent2TwentiethRejoin.reentry20Time +
    DRegular.accumulated 12588 seed21

/-- The twenty-first exceptional input is reached from the genuine blank
    tape, conditional only on the preceding source-certified chain. -/
theorem blank_twentyfirst_exception :
    ObsEq (run exception21Time blank)
      (DRegularSource.sourceSection ⟨9*t21+4,8,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent2TwentiethRejoin.reentry20Time
    12588 seed21 ⟨9*t21+4,8,1⟩
  · constructor
    · change 8*BB6.Agent2TwentiethRejoin.k20+9 ≥ 2
      omega
    · left
      change (8 : Nat) ≠ 0
      omega
  · exact terminal12588_exact
  · exact BB6.Agent2TwentiethRejoin.blank_twentieth_reentry

def packet21Time : Nat :=
  BB6.Agent32EAll.duration (3*t21) 7 +
    BB6.Agent25BGeneral.bCost t21

def reentry21Time : Nat := exception21Time + packet21Time

/-- Original-source E/B reentry of the twenty-first exception. The input
    has E index 3*t21 and q=8; the universal p=6 E/B theorem returns to
    the regular language at L(64*t21+33,1,5). -/
theorem blank_twentyfirst_reentry :
    ObsEq (run reentry21Time blank)
      (DRegularSource.sourceSection ⟨64*t21+33,1,5⟩) := by
  exact source_chain exception21Time packet21Time blank
    (DRegularSource.sourceSection ⟨9*t21+4,8,1⟩)
    (DRegularSource.sourceSection ⟨64*t21+33,1,5⟩)
    blank_twentyfirst_exception
    (by simpa only [packet21Time] using
      (BB6.Agent25BGeneral.exceptional_EB_general t21 6))

#print axioms terminal12588_exact
#print axioms t21_mod27
#print axioms blank_twentyfirst_exception
#print axioms blank_twentyfirst_reentry

end BB6.Agent2TwentyFirstRoot
