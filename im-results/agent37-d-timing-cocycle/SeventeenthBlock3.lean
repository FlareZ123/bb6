import SeventeenthBlock2
import SeventeenthFirstHalf
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SeventeenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

/-- The 304-section remainder closes the first 1,328-section arithmetic
    half at the already recorded middle17 state. -/
def block17_3 : DRegular.L :=
  BB6.Agent2SeventeenthArithmetic.middle17

theorem block17_3_exact :
    DRegular.run 304 block17_2 = some block17_3 := by
  rw [BB6.DRegularFast.fastRun_correct 304 block17_2 block17_2_canon]
  decide

theorem block17_3_canon : DRegular.Canon block17_3 :=
  BB6.DRegularFast.run_canon 304 block17_2 block17_3
    block17_2_canon block17_3_exact

def block17_3Time : Nat :=
  block17_2Time + DRegular.accumulated 304 block17_2

/-- The authentic blank-root orbit now reaches the exact first-half
    checkpoint without one 1,328-step transport proof. -/
theorem blank_seventeenth_block3 :
    ObsEq (run block17_3Time blank)
      (DRegularSource.sourceSection block17_3) := by
  exact BB6.Agent25RootChain.extend_regular blank
    block17_2Time 304 block17_2 block17_3
    block17_2_canon block17_3_exact blank_seventeenth_block2

#print axioms block17_3_exact
#print axioms blank_seventeenth_block3

end BB6.Agent2SeventeenthRoot
