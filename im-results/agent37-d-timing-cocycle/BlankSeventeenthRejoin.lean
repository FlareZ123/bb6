import Lean.Elab.Tactic.Omega
import SeventeenthBlock6
import SeventeenthTerminalCertificate
import ExceptionalE7ThirdReturn

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SeventeenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def packet17Time : Nat :=
  BB6.Agent2E7ThirdReturn.totalTime
    (BB6.Agent2SeventeenthArithmetic.t17 / 3) 2

def reentry17Time : Nat := block17_6Time + packet17Time

private theorem mul_div_from_mod27 (n : Nat) (h : n % 27 = 6) :
    27 * (n / 3) + 7 = 9 * n + 7 := by
  have hdiv : n = 3 * (n / 3) := by
    have h3 : n % 3 = 0 := by omega
    have hdiv := Nat.mod_add_div n 3
    rw [h3] at hdiv
    omega
  omega

/-- The seventeenth E input is exactly the terminal arithmetic section,
    expressed in the E7 packet's (u,q) coordinates. -/
theorem seventeenth_source_start :
    BB6.Agent2E7ThirdReturn.sourceStart
      (BB6.Agent2SeventeenthArithmetic.t17 / 3) 2 =
    DRegularSource.sourceSection
      BB6.Agent2SeventeenthArithmetic.terminal2656 := by
  change DRegularSource.sourceSection
      ⟨27 * (BB6.Agent2SeventeenthArithmetic.t17 / 3) + 7, 7, 1⟩ =
    DRegularSource.sourceSection
      BB6.Agent2SeventeenthArithmetic.terminal2656
  have ha := mul_div_from_mod27 BB6.Agent2SeventeenthArithmetic.t17
    BB6.Agent2SeventeenthArithmetic.terminal2656_signature.2
  have hsig := BB6.Agent2SeventeenthArithmetic.terminal2656_signature.1
  have hstruct :
      (⟨27 * (BB6.Agent2SeventeenthArithmetic.t17 / 3) + 7, 7, 1⟩ : DRegular.L) =
        BB6.Agent2SeventeenthArithmetic.terminal2656 := by
    calc
      ⟨27 * (BB6.Agent2SeventeenthArithmetic.t17 / 3) + 7, 7, 1⟩ =
          ⟨9 * BB6.Agent2SeventeenthArithmetic.t17 + 7, 7, 1⟩ := by
        simpa only [ha]
      _ = BB6.Agent2SeventeenthArithmetic.terminal2656 := hsig.symm
  exact congrArg DRegularSource.sourceSection hstruct

/-- The genuine blank D orbit passes the seventeenth exceptional E input,
    uses its exact three-return E/E/A source packet, and rejoins L(a,3,2). -/
theorem blank_seventeenth_reentry :
    ObsEq (run reentry17Time blank)
      (DRegularSource.sourceSection
        ⟨8 * (64 * (BB6.Agent2SeventeenthArithmetic.t17 / 3) + 10) + 39,
          3, 2⟩) := by
  have hpacket :=
    BB6.Agent2E7ThirdReturn.exceptional_EEA_rejoin
      (BB6.Agent2SeventeenthArithmetic.t17 / 3) 2 (by decide)
  rw [seventeenth_source_start] at hpacket
  exact source_chain block17_6Time packet17Time blank
    (DRegularSource.sourceSection BB6.Agent2SeventeenthArithmetic.terminal2656)
    (BB6.Agent2E7ThirdReturn.sourceEnd
      (BB6.Agent2SeventeenthArithmetic.t17 / 3) 2)
    blank_seventeenth_block6
    (by simpa only [packet17Time] using hpacket)

#print axioms blank_seventeenth_reentry

end BB6.Agent2SeventeenthRoot
