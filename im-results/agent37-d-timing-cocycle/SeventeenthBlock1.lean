import BlankSixteenthRejoin
import SeventeenthFirstHalf
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SeventeenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

/-- First 512 arithmetic sections after the sixteenth authentic blank-root
    reentry.  The residue-reduced evaluator makes this checkpoint finite and
    independently replayable. -/
def block17_1 : DRegular.L :=
  (BB6.DRegularFast.fastRun 512 BB6.Agent2SeventeenthArithmetic.seed17).getD ⟨9, 0, 0⟩

theorem block17_1_exact :
    DRegular.run 512 BB6.Agent2SeventeenthArithmetic.seed17 = some block17_1 := by
  rw [BB6.DRegularFast.fastRun_correct 512
    BB6.Agent2SeventeenthArithmetic.seed17
    BB6.Agent2SeventeenthArithmetic.seed17_canon]
  decide

theorem block17_1_canon : DRegular.Canon block17_1 :=
  BB6.DRegularFast.run_canon 512 BB6.Agent2SeventeenthArithmetic.seed17
    block17_1 BB6.Agent2SeventeenthArithmetic.seed17_canon block17_1_exact

def block17_1Time : Nat :=
  BB6.Agent2SixteenthRoot.reentry16Time +
    DRegular.accumulated 512 BB6.Agent2SeventeenthArithmetic.seed17

/-- Lift the first 512 arithmetic steps to the authentic blank-root orbit. -/
theorem blank_seventeenth_block1 :
    ObsEq (run block17_1Time blank)
      (DRegularSource.sourceSection block17_1) := by
  exact BB6.Agent25RootChain.extend_regular blank
    BB6.Agent2SixteenthRoot.reentry16Time
    512 BB6.Agent2SeventeenthArithmetic.seed17 block17_1
    BB6.Agent2SeventeenthArithmetic.seed17_canon block17_1_exact
    BB6.Agent2SixteenthRoot.blank_sixteenth_reentry

#print axioms block17_1_exact
#print axioms blank_seventeenth_block1

end BB6.Agent2SeventeenthRoot
