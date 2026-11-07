import Lean.Elab.Tactic.Omega
import BlankTwentyFourthRejoin
import ExceptionalBGeneral

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2TwentyFifthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def seed25 : DRegular.L := BB6.Agent2TwentyFourthRoot.seed25

def terminal1718 : DRegular.L :=
  (DRegular.run 1718 seed25).getD ⟨9,0,0⟩

def t25 : Nat := (terminal1718.a-4)/9

theorem terminal1718_certificate :
    DRegular.run 1718 seed25 = some ⟨9*t25+4,8,1⟩ ∧
      t25 % 27 = 16 := by
  decide

theorem terminal1718_exact :
    DRegular.run 1718 seed25 = some ⟨9*t25+4,8,1⟩ :=
  terminal1718_certificate.1

theorem t25_mod27 : t25 % 27 = 16 :=
  terminal1718_certificate.2

def exception25Time (T22 Tnorm24 : Nat) : Nat :=
  BB6.Agent2TwentyFourthRoot.reentry24Time T22 Tnorm24 +
    DRegular.accumulated 1718 seed25

/-- Extend any witnessed twenty-fourth reentry through the next D-regular run. -/
theorem blank_twenty_fifth_exception_from (T22 Tnorm24 : Nat)
    (h24 : ObsEq
      (run (BB6.Agent2TwentyFourthRoot.reentry24Time T22 Tnorm24) blank)
      (DRegularSource.sourceSection seed25)) :
    ObsEq (run (exception25Time T22 Tnorm24) blank)
      (DRegularSource.sourceSection ⟨9*t25+4,8,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    (BB6.Agent2TwentyFourthRoot.reentry24Time T22 Tnorm24)
    1718 seed25 ⟨9*t25+4,8,1⟩
  · constructor
    · change
        BB6.Agent2PacketZeroBoundary.aZeroUnary
          BB6.Agent2TwentyFourthRoot.k24
          BB6.Agent2TwentyFourthRoot.normalized24.q
          BB6.Agent2TwentyFourthRoot.r24 ≥ 2
      simp [BB6.Agent2PacketZeroBoundary.aZeroUnary]
      omega
    · right
      rfl
  · exact terminal1718_exact
  · exact h24

def packet25Time : Nat :=
  BB6.Agent32EAll.duration (3*t25) 7 +
    BB6.Agent25BGeneral.bCost t25

def reentry25Time (T22 Tnorm24 : Nat) : Nat :=
  exception25Time T22 Tnorm24 + packet25Time

/-- The q=8 exceptional B return closes the twenty-fifth root episode. -/
theorem blank_twenty_fifth_reentry :
    ∃ T22 Tnorm24,
      ObsEq (run (reentry25Time T22 Tnorm24) blank)
        (DRegularSource.sourceSection ⟨64*t25+33,1,5⟩) := by
  obtain ⟨T22,Tnorm24,h24⟩ :=
    BB6.Agent2TwentyFourthRoot.blank_twenty_fourth_reentry
  have h25 := blank_twenty_fifth_exception_from T22 Tnorm24 h24
  have hEB :
      ObsEq
        (run packet25Time
          (DRegularSource.sourceSection ⟨9*t25+4,8,1⟩))
        (DRegularSource.sourceSection ⟨64*t25+33,1,5⟩) := by
    simpa [packet25Time] using
      (BB6.Agent25BGeneral.exceptional_EB_general t25 6)
  exact ⟨T22,Tnorm24,source_chain (exception25Time T22 Tnorm24)
    packet25Time blank
    (DRegularSource.sourceSection ⟨9*t25+4,8,1⟩)
    (DRegularSource.sourceSection ⟨64*t25+33,1,5⟩)
    h25 hEB⟩

#print axioms terminal1718_exact
#print axioms t25_mod27
#print axioms blank_twenty_fifth_exception_from
#print axioms blank_twenty_fifth_reentry

end BB6.Agent2TwentyFifthRoot
