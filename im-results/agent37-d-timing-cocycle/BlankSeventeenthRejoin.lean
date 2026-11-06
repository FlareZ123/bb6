import Lean.Elab.Tactic.Omega
import BlankSixteenthRejoin
import ExceptionalE7ThirdReturn

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SeventeenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def seed17 : DRegular.L :=
  ⟨64*BB6.Agent2SixteenthRoot.t16+27,1,5⟩

def terminal2656 : DRegular.L :=
  (DRegular.run 2656 seed17).getD ⟨9,0,0⟩

def t17 : Nat := (terminal2656.a-7)/9

/-- One kernel computation certifies both the exact seventeenth
    exceptional state and the residue needed by its three-return source proof. -/
theorem terminal2656_certificate :
    DRegular.run 2656 seed17 = some ⟨9*t17+7,7,1⟩ ∧
      t17 % 27 = 6 := by decide

theorem terminal2656_exact :
    DRegular.run 2656 seed17 = some ⟨9*t17+7,7,1⟩ :=
  terminal2656_certificate.1

/-- The exceptional parameter lies in the k≡1, t≡0 (mod 3), q=6
    three-return subfamily. -/
theorem t17_mod27 : t17 % 27 = 6 :=
  terminal2656_certificate.2

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
  BB6.Agent2E7ThirdReturn.totalTime u17

def reentry17Time : Nat := exception17Time+packet17Time

/-- The genuine blank D orbit passes the seventeenth exceptional E input,
    uses its exact three-return E/E/A source packet, and rejoins pure unary. -/
theorem blank_seventeenth_reentry :
    ObsEq (run reentry17Time blank)
      (DRegularSource.sourceSection
        ⟨8*(64*u17+10)+45,0,0⟩) := by
  have hstart :
      BB6.Agent2E7ThirdReturn.sourceStart u17 =
        DRegularSource.sourceSection ⟨9*t17+7,7,1⟩ := by
    unfold BB6.Agent2E7ThirdReturn.sourceStart
    congr 1
    omega
  have hpacket :=
    BB6.Agent2E7ThirdReturn.exceptional_EEA_rejoin u17
  rw [hstart] at hpacket
  exact source_chain exception17Time packet17Time blank
    (DRegularSource.sourceSection ⟨9*t17+7,7,1⟩)
    (DRegularSource.sourceEnd u17)
    blank_seventeenth_exception
    (by simpa only [packet17Time] using hpacket)

#print axioms terminal2656_exact
#print axioms t17_mod27
#print axioms blank_seventeenth_exception
#print axioms blank_seventeenth_reentry

end BB6.Agent2SeventeenthRoot
