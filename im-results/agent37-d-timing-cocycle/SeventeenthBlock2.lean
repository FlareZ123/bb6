import SeventeenthBlock1
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SeventeenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

/-- Second 512-section checkpoint, beginning at the first block's exact
    source-certified endpoint. -/
def block17_2 : DRegular.L :=
  (BB6.DRegularFast.fastRun 512 block17_1).getD ⟨9, 0, 0⟩

theorem block17_2_exact :
    DRegular.run 512 block17_1 = some block17_2 := by
  rw [BB6.DRegularFast.fastRun_correct 512 block17_1 block17_1_canon]
  decide

theorem block17_2_canon : DRegular.Canon block17_2 :=
  BB6.DRegularFast.run_canon 512 block17_1 block17_2
    block17_1_canon block17_2_exact

def block17_2Time : Nat :=
  block17_1Time + DRegular.accumulated 512 block17_1

/-- Lift the second 512 arithmetic steps from the first certified section. -/
theorem blank_seventeenth_block2 :
    ObsEq (run block17_2Time blank)
      (DRegularSource.sourceSection block17_2) := by
  exact BB6.Agent25RootChain.extend_regular blank
    block17_1Time 512 block17_1 block17_2
    block17_1_canon block17_2_exact blank_seventeenth_block1

#print axioms block17_2_exact
#print axioms blank_seventeenth_block2

end BB6.Agent2SeventeenthRoot
