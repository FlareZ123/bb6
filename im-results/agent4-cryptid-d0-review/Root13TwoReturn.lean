import Root13Section
import ESecondSource

set_option maxHeartbeats 5000000
set_option maxRecDepth 55000

namespace BB6.Agent4Root13TwoReturn

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent4Root13Section
open BB6.Agent31SecondSource
open DRegularSource

/-- The authentic blank-root trajectory, from the fifth reentry, reaches the
seed-9 E-exception input and then follows the two independently source-proved
exceptional returns to the first packet outside the regular L language. The
root-to-input bridge is Agent 4's 4,484+10 DRegular source lift; the two-return
tail is Agent 31's arbitrary-parameter original-source composition. -/
theorem root13_to_two_return_escape_original :
    ObsEq
      (run
        (BB6.Agent25FifthRoot.fifthReentryTime +
          DRegular.accumulated 4484 BB6.Agent25SixthRoot.seed +
          DRegular.accumulated 10 root13Section +
          firstCost BB6.Agent25SixthRoot.t6 1 +
          secondCost BB6.Agent25SixthRoot.t6)
        blank)
      (finish BB6.Agent25SixthRoot.t6 1) := by
  have hroot := root13_to_sixth_exception_original
  have ha : 9*BB6.Agent25SixthRoot.t6+7-2 =
      9*BB6.Agent25SixthRoot.t6+5 := by omega
  have hk : 3*(3*BB6.Agent25SixthRoot.t6+1)+2 =
      9*BB6.Agent25SixthRoot.t6+5 := by omega
  have hstart :
      DRegularSource.sourceSection
        ⟨9*BB6.Agent25SixthRoot.t6+7,4,1⟩ =
      start BB6.Agent25SixthRoot.t6 1 := by
    simp [DRegularSource.sourceSection, start, ha, hk,
      CryptidBoundary.oppairs, CryptidBoundary.pairs,
      List.append_assoc]
  have hroot' :
      ObsEq
        (run
          (BB6.Agent25FifthRoot.fifthReentryTime +
            DRegular.accumulated 4484 BB6.Agent25SixthRoot.seed +
            DRegular.accumulated 10 root13Section)
          blank)
        (start BB6.Agent25SixthRoot.t6 1) := by
    simpa [hstart] using hroot
  simpa [Nat.add_assoc] using
    (source_chain
      (BB6.Agent25FifthRoot.fifthReentryTime +
        DRegular.accumulated 4484 BB6.Agent25SixthRoot.seed +
        DRegular.accumulated 10 root13Section)
      (firstCost BB6.Agent25SixthRoot.t6 1 +
        secondCost BB6.Agent25SixthRoot.t6)
      blank
      (start BB6.Agent25SixthRoot.t6 1)
      (finish BB6.Agent25SixthRoot.t6 1)
      hroot'
      (two_returns_source BB6.Agent25SixthRoot.t6 1))

#print axioms root13_to_two_return_escape_original

end BB6.Agent4Root13TwoReturn
