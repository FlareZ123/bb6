import Lean.Elab.Tactic.Omega
import BlankSixteenthRejoin
import SeventeenthSecondHalf
import ExceptionalE7ThirdReturn
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SeventeenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def seed17 : L := BB6.Agent2SeventeenthArithmetic.seed17

def terminal2656 : L := BB6.Agent2SeventeenthArithmetic.terminal2656

def t17 : Nat := BB6.Agent2SeventeenthArithmetic.t17

theorem terminal2656_certificate :
    run 2656 seed17 = some ⟨9 * t17 + 7, 7, 1⟩ ∧ t17 % 27 = 6 := by
  have htotal : run 2656 seed17 = some terminal2656 := by
    rw [show 2656 = 1328 + 1328 by omega,
      BB6.DRegularFast.run_add 1328 1328 seed17,
      BB6.Agent2SeventeenthArithmetic.middle17_exact]
    simpa [terminal2656] using
      BB6.Agent2SeventeenthArithmetic.terminal2656_half_exact
  rcases BB6.Agent2SeventeenthArithmetic.terminal2656_signature with ⟨hsig, hmod⟩
  constructor
  · rw [hsig] at htotal
    simpa [t17] using htotal
  · simpa [t17] using hmod

def u17 : Nat := t17/3

theorem t17_eq_three_u17 : t17=3*u17 := by
  have h := t17_mod27
  dsimp [u17]
  omega

def exception17Time : Nat :=
  BB6.Agent2SixteenthRoot.reentry16Time +
    DRegular.accumulated 2656 seed17

theorem blank_seventeenth_exception :
    ObsEq (run exception17Time blank)
      (DRegularSource.sourceSection ⟨9*t17+7,7,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent2SixteenthRoot.reentry16Time
    2656 seed17 ⟨9*t17+7,7,1⟩
  · constructor
    · change 64*BB6.Agent2SixteenthRoot.t16+27 ≥ 2
      omega
    · left
      change (1:Nat) ≠ 0
      omega
  · exact terminal2656_exact
  · exact BB6.Agent2SixteenthRoot.blank_sixteenth_reentry

def packet17Time : Nat :=
  BB6.Agent2E7ThirdReturn.totalTime u17 2

def reentry17Time : Nat := exception17Time+packet17Time

/-- The genuine blank D orbit passes the seventeenth exceptional E input,
    uses its exact three-return E/E/A source packet, and rejoins L(a,3,2). -/
theorem blank_seventeenth_reentry :
    ObsEq (run reentry17Time blank)
      (DRegularSource.sourceSection
        ⟨8*(64*u17+10)+39,3,2⟩) := by
  have hstart :
      BB6.Agent2E7ThirdReturn.sourceStart u17 2 =
        DRegularSource.sourceSection ⟨9*t17+7,7,1⟩ := by
    unfold BB6.Agent2E7ThirdReturn.sourceStart
    congr 1
  have hpacket :=
    BB6.Agent2E7ThirdReturn.exceptional_EEA_rejoin u17 2 (by omega)
  rw [hstart] at hpacket
  exact source_chain exception17Time packet17Time blank
    (DRegularSource.sourceSection ⟨9*t17+7,7,1⟩)
    (BB6.Agent2E7ThirdReturn.sourceEnd u17 2)
    blank_seventeenth_exception
    (by simpa only [packet17Time] using hpacket)

#print axioms terminal2656_exact
#print axioms t17_mod27
#print axioms blank_seventeenth_exception
#print axioms blank_seventeenth_reentry

end BB6.Agent2SeventeenthRoot
