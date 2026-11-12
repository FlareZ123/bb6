import Lean.Elab.Tactic.Omega
import BlankTwentySeventhRejoin
import ExceptionalBGeneral
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2TwentyEighthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def seed28 : DRegular.L := BB6.Agent2TwentySeventhRoot.seed28

def terminal2590 : DRegular.L :=
  (BB6.DRegularFast.fastRun 2590 seed28).getD ⟨9,0,0⟩

def t28 : Nat := (terminal2590.a-4)/9

theorem terminal2590_certificate :
    DRegular.run 2590 seed28 = some ⟨9*t28+4,9,1⟩ ∧
      t28 % 27 = 23 := by
  have hcanon : DRegular.Canon seed28 := by
    constructor
    · dsimp [seed28, BB6.Agent2TwentySeventhRoot.seed28,
        BB6.Agent2PacketZeroBoundary.aZeroUnary]
      omega
    · right
      rfl
  rw [BB6.DRegularFast.fastRun_correct 2590 seed28 hcanon]
  decide

theorem terminal2590_exact :
    DRegular.run 2590 seed28 = some ⟨9*t28+4,9,1⟩ :=
  terminal2590_certificate.1

theorem t28_mod27 : t28 % 27 = 23 :=
  terminal2590_certificate.2

def exception28Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  BB6.Agent2TwentySeventhRoot.reentry27Time T22 Tnorm24 Tnorm27 +
    DRegular.accumulated 2590 seed28

/-- Extend the source-certified twenty-seventh reentry through the next
    exact D-regular segment. -/
theorem blank_twenty_eighth_exception_from (T22 Tnorm24 Tnorm27 : Nat)
    (h27 : ObsEq
      (run (BB6.Agent2TwentySeventhRoot.reentry27Time
        T22 Tnorm24 Tnorm27) blank)
      (DRegularSource.sourceSection seed28)) :
    ObsEq (run (exception28Time T22 Tnorm24 Tnorm27) blank)
      (DRegularSource.sourceSection ⟨9*t28+4,9,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    (BB6.Agent2TwentySeventhRoot.reentry27Time T22 Tnorm24 Tnorm27)
    2590 seed28 ⟨9*t28+4,9,1⟩
  · constructor
    · dsimp [seed28, BB6.Agent2TwentySeventhRoot.seed28,
        BB6.Agent2PacketZeroBoundary.aZeroUnary]
      omega
    · right
      rfl
  · exact terminal2590_exact
  · exact h27

theorem blank_twenty_eighth_exception :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq (run (exception28Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection ⟨9*t28+4,9,1⟩) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h27⟩ :=
    BB6.Agent2TwentySeventhRoot.blank_twenty_seventh_reentry
  exact ⟨T22,Tnorm24,Tnorm27,
    blank_twenty_eighth_exception_from T22 Tnorm24 Tnorm27 h27⟩

/-- The E/B universal source return sends the 28th exception to
    L(64*t28+35,1,5). -/
def seed29 : DRegular.L := ⟨64*t28+35,1,5⟩

def reentry28Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  exception28Time T22 Tnorm24 Tnorm27 +
    (BB6.Agent32EAll.duration (3*t28) 8 +
      BB6.Agent25BGeneral.bCost t28)

theorem blank_twenty_eighth_reentry :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq (run (reentry28Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection seed29) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h28⟩ := blank_twenty_eighth_exception
  have hEB := BB6.Agent25BGeneral.exceptional_EB_general t28 7
  have hroot : ObsEq
      (run (BB6.Agent32EAll.duration (3*t28) 8 +
        BB6.Agent25BGeneral.bCost t28)
        (DRegularSource.sourceSection ⟨9*t28+4,9,1⟩))
      (DRegularSource.sourceSection seed29) := by
    simpa [seed29] using hEB
  exact ⟨T22,Tnorm24,Tnorm27,
    source_chain (exception28Time T22 Tnorm24 Tnorm27)
      (BB6.Agent32EAll.duration (3*t28) 8 +
        BB6.Agent25BGeneral.bCost t28)
      blank
      (DRegularSource.sourceSection ⟨9*t28+4,9,1⟩)
      (DRegularSource.sourceSection seed29) h28 hroot⟩

#print axioms terminal2590_exact
#print axioms t28_mod27
#print axioms blank_twenty_eighth_exception
#print axioms blank_twenty_eighth_reentry

end BB6.Agent2TwentyEighthRoot
