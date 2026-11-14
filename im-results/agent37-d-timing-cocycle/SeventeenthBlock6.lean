import SeventeenthBlock5
import SeventeenthSecondHalf
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SeventeenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

/-- Final 304-section remainder reaches the independently computed
    terminal state of the second 1,328-section half. -/
def block17_6 : DRegular.L :=
  BB6.Agent2SeventeenthArithmetic.terminal2656

theorem block17_6_exact :
    DRegular.run 304 block17_5 = some block17_6 := by
  have h512 : DRegular.run 512 BB6.Agent2SeventeenthArithmetic.middle17 =
      some block17_4 := by
    simpa [block17_3] using block17_4_exact
  have h1024 : DRegular.run 1024 BB6.Agent2SeventeenthArithmetic.middle17 =
      some block17_5 := by
    calc
      DRegular.run 1024 BB6.Agent2SeventeenthArithmetic.middle17 =
          (DRegular.run 512 BB6.Agent2SeventeenthArithmetic.middle17).bind
            (DRegular.run 512) := by
              simpa using (BB6.DRegularFast.run_add 512 512
                BB6.Agent2SeventeenthArithmetic.middle17)
      _ = (some block17_4).bind (DRegular.run 512) := by rw [h512]
      _ = DRegular.run 512 block17_4 := rfl
      _ = some block17_5 := block17_5_exact
  have hcomp :
      DRegular.run 1328 BB6.Agent2SeventeenthArithmetic.middle17 =
        DRegular.run 304 block17_5 := by
    calc
      DRegular.run 1328 BB6.Agent2SeventeenthArithmetic.middle17 =
          (DRegular.run 1024 BB6.Agent2SeventeenthArithmetic.middle17).bind
            (DRegular.run 304) := by
              simpa using (BB6.DRegularFast.run_add 1024 304
                BB6.Agent2SeventeenthArithmetic.middle17)
      _ = (some block17_5).bind (DRegular.run 304) := by rw [h1024]
      _ = DRegular.run 304 block17_5 := rfl
  calc
    DRegular.run 304 block17_5 =
        DRegular.run 1328 BB6.Agent2SeventeenthArithmetic.middle17 := hcomp.symm
    _ = some block17_6 := by
      simpa [block17_6] using
        BB6.Agent2SeventeenthArithmetic.terminal2656_half_exact

theorem block17_6_canon : DRegular.Canon block17_6 :=
  BB6.DRegularFast.run_canon 304 block17_5 block17_6
    block17_5_canon block17_6_exact

def block17_6Time : Nat :=
  block17_5Time + DRegular.accumulated 304 block17_5

theorem blank_seventeenth_block6 :
    ObsEq (run block17_6Time blank)
      (DRegularSource.sourceSection block17_6) := by
  exact BB6.Agent25RootChain.extend_regular blank
    block17_5Time 304 block17_5 block17_6
    block17_5_canon block17_6_exact blank_seventeenth_block5

#print axioms block17_6_exact
#print axioms blank_seventeenth_block6

end BB6.Agent2SeventeenthRoot
