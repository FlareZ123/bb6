import SeventeenthBlock3
import SeventeenthFirstHalf
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SeventeenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

/-- First 512-section block of the second 1,328-section half. -/
def block17_4 : DRegular.L :=
  (BB6.DRegularFast.fastRun 512 block17_3).getD ⟨9, 0, 0⟩

theorem block17_4_exact :
    DRegular.run 512 block17_3 = some block17_4 := by
  rw [BB6.DRegularFast.fastRun_correct 512 block17_3 block17_3_canon]
  decide

theorem block17_4_canon : DRegular.Canon block17_4 :=
  BB6.DRegularFast.run_canon 512 block17_3 block17_4
    block17_3_canon block17_4_exact

def block17_4Time : Nat :=
  block17_3Time + DRegular.accumulated 512 block17_3

theorem blank_seventeenth_block4 :
    ObsEq (run block17_4Time blank)
      (DRegularSource.sourceSection block17_4) := by
  exact BB6.Agent25RootChain.extend_regular blank
    block17_3Time 512 block17_3 block17_4
    block17_3_canon block17_4_exact blank_seventeenth_block3

#print axioms block17_4_exact
#print axioms blank_seventeenth_block4

end BB6.Agent2SeventeenthRoot
