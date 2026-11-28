import Raw40LateCrossingTripleEntry
import Raw40LateCrossingTripleLeft
import Raw40LateCrossingTripleRightA
import Raw40LateCrossingTripleRightB
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent19Raw40LateCrossing.C1REM1096
open BB6Coverage Agent42Crossing Agent19OrientedCrossing Agent50Zipper
def cert : Certificate := ⟨leftCells,headCell,[seg0,seg1,seg2,seg3,seg4,seg5,seg6]⟩
theorem bankOK : certOK oriented cert := by
  refine ⟨headOK,leftCellsOK,?_⟩
  exact ⟨right0OK,pump0,right1OK,pump1,right2OK,pump2,right3OK,pump3,right4OK,pump4,right5OK,pump5,right6OK,pump6,rfl⟩
theorem checkedCert : checkedFrom oriented cert (initialZ true) 483904 (-1298) := by
  refine ⟨bankOK,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · unfold entryOKFrom
    rw [entryRun]
    decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_oriented true true table cert 483904 (-1298) checkedCert m hm
#print axioms bankOK
#print axioms never

end BB6Coverage.Agent19Raw40LateCrossing.C1REM1096
