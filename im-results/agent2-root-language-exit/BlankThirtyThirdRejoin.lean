import Lean.Elab.Tactic.Omega
import BlankThirtySecondRejoin
import Exception33Q5Rejoin
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2ThirtyThirdRejoin

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent2ThirtySecondRejoin
open BB6.Agent25Exception33Q5
open BB6.Agent25RootChain

/-- The exact regular-model state after 9,276 transitions from seed33. -/
def terminal9276 : DRegular.L :=
  (BB6.DRegularFast.fastRun 9276 seed33).getD ⟨9,0,0⟩

/-- The exception-33 parameter in the corrected a = 27*u + 7 chart. -/
def u33 : Nat := (terminal9276.a - 7) / 27

/-- Kernel-computed transition and residue certificate for exception 33. -/
theorem terminal9276_certificate :
    DRegular.run 9276 seed33 = some ⟨27*u33+7,5,1⟩ ∧
      terminal9276.a % 59049 = 49579 := by
  rw [BB6.DRegularFast.fastRun_correct 9276 seed33 seed33_canon]
  decide

theorem terminal9276_shape :
    terminal9276 = ⟨27*u33+7,5,1⟩ := by
  have hfast :
      BB6.DRegularFast.fastRun 9276 seed33 =
        some ⟨27*u33+7,5,1⟩ := by
    rw [← BB6.DRegularFast.fastRun_correct 9276 seed33 seed33_canon]
    exact terminal9276_certificate.1
  simp [terminal9276, hfast]

/-- The new unary seed produced by the original-source exception-33 return. -/
def seed34 : DRegular.L := ⟨512*u33+129,0,0⟩

theorem seed34_canon : DRegular.Canon seed34 := by
  constructor
  · dsimp [seed34]
    omega
  · right
    rfl

def exception33Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  reentry32Time T22 Tnorm24 Tnorm27 +
    DRegular.accumulated 9276 seed33

theorem blank_thirty_third_exception_from
    (T22 Tnorm24 Tnorm27 : Nat)
    (h32 : ObsEq
      (run (reentry32Time T22 Tnorm24 Tnorm27) blank)
      (DRegularSource.sourceSection seed33)) :
    ObsEq
      (run (exception33Time T22 Tnorm24 Tnorm27) blank)
      (DRegularSource.sourceSection terminal9276) := by
  have hrun : DRegular.run 9276 seed33 = some terminal9276 := by
    rw [terminal9276_shape]
    exact terminal9276_certificate.1
  exact Agent25RootChain.extend_regular blank
    (reentry32Time T22 Tnorm24 Tnorm27)
    9276 seed33 terminal9276 seed33_canon hrun h32

/-- Extend the authentic blank-root prefix through the 9,276-step
    regular segment to the corrected q=5 exception-33 source section. -/
theorem blank_thirty_third_exception :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq
        (run (exception33Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection terminal9276) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h32⟩ :=
    BB6.Agent2ThirtySecondRejoin.blank_thirty_second_reentry
  exact ⟨T22,Tnorm24,Tnorm27,
    blank_thirty_third_exception_from T22 Tnorm24 Tnorm27 h32⟩

def duration33 : Nat :=
  eAllTime u33 + eThreeTime u33 + aCodeTime u33

def reentry33Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  exception33Time T22 Tnorm24 Tnorm27 + duration33

/-- The corrected exception-33 EAllDouble -> E-three -> A-code source
    composition returns to a pure-unary regular section. -/
theorem blank_thirty_third_reentry :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq
        (run (reentry33Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection seed34) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h33⟩ :=
    blank_thirty_third_exception
  have hroot :
      ObsEq
        (run duration33
          (DRegularSource.sourceSection terminal9276))
        (DRegularSource.sourceSection seed34) := by
    rw [terminal9276_shape]
    simpa [duration33, seed34, BB6.Agent25Exception33Q5.sourceStart] using
      (BB6.Agent25Exception33Q5.exception33_q5_rejoin u33)
  exact ⟨T22,Tnorm24,Tnorm27,
    source_chain (exception33Time T22 Tnorm24 Tnorm27)
      duration33 blank
      (DRegularSource.sourceSection terminal9276)
      (DRegularSource.sourceSection seed34) h33 hroot⟩

#print axioms terminal9276_certificate
#print axioms blank_thirty_third_exception
#print axioms blank_thirty_third_reentry

end BB6.Agent2ThirtyThirdRejoin
