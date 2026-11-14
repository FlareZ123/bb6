import SeventeenthBlock4
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SeventeenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

/-- Second 512-section block of the second arithmetic half. -/
def block17_5 : DRegular.L :=
  (BB6.DRegularFast.fastRun 512 block17_4).getD ⟨9, 0, 0⟩

theorem block17_5_exact :
    DRegular.run 512 block17_4 = some block17_5 := by
  rw [BB6.DRegularFast.fastRun_correct 512 block17_4 block17_4_canon]
  decide

theorem block17_5_canon : DRegular.Canon block17_5 :=
  BB6.DRegularFast.run_canon 512 block17_4 block17_5
    block17_4_canon block17_5_exact

def block17_5Time : Nat :=
  block17_4Time + DRegular.accumulated 512 block17_4

theorem blank_seventeenth_block5 :
    ObsEq (run block17_5Time blank)
      (DRegularSource.sourceSection block17_5) := by
  exact BB6.Agent25RootChain.extend_regular blank
    block17_4Time 512 block17_4 block17_5
    block17_4_canon block17_5_exact blank_seventeenth_block4

#print axioms block17_5_exact
#print axioms blank_seventeenth_block5

end BB6.Agent2SeventeenthRoot
