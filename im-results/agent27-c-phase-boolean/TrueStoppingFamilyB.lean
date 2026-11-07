import InfiniteStrictB
import Lean.Elab.Tactic.Omega

namespace BB6.Agent27InfiniteStrictB

/-- The explicit right counter of each syntactically genuine immediate
    stopping state of the original C section machine. -/
def stopCounter (t : Nat) : Nat :=
  2^(2*11+2)*(highIndex t+3) - (highIndex t+3*11+5)

theorem stopCounter_equation (t : Nat) :
    stopCounter t + highIndex t+3*11+5 =
       2^(2*11+2)*(highIndex t+3) := by
  have hp : (2:Nat)^(2*11+2) = 16777216 := by decide
  have hb : highIndex t+3*11+5 ≤ 2^(2*11+2)*(highIndex t+3) := by
    rw [hp]
    dsimp [highIndex]
    omega
  exact Nat.sub_add_cancel hb

/-- The whole infinite strict family consists of actual one-step
    halting inputs of the unmodified original C source section.
    Blank-root attainability is a distinct question. -/
theorem source_immediately_stops (t : Nat) :
  BB6.Agent46.secNext (2*highIndex t+3,stopCounter t) = none := by
  apply (BB6.Agent15.section_halts_iff_parametric _ _).mpr
  exact Or.inr (Or.inr ⟨highIndex t,11,rfl,stopCounter_equation t⟩)

/-- These genuine stopping states are excluded from the original
    blank-root orbit by the all-phase cone. -/
theorem stop_states_unreachable (t : Nat) :
  ¬BB6.Agent3.CReach (2*highIndex t+3) (stopCounter t) := by
  intro hreach
  have hphase : (highIndex t+3*11+3)%2^(8+4) = 13*2^8 := by
    have h8 : (2:Nat)^8=256 := by decide
    have h12 : (2:Nat)^(8+4)=4096 := by decide
    rw [h8,h12]
    dsimp [highIndex]
    omega
  have hmod : highIndex t%16=(12+2*8)%16 := by
    dsimp [highIndex]
    omega
  exact BB6.Agent46.high_all_phase_B_no_blank 8 (highIndex t) 11
    (stopCounter t) (by omega) (by omega) hmod hphase
    (stopCounter_equation t) hreach

#print axioms source_immediately_stops
#print axioms stop_states_unreachable
end BB6.Agent27InfiniteStrictB
