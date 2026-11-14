import TM63M1OddRst1PrimeContinuation
import M1OneQ4Prefix
import CostRecurrence
import Lean.Elab.Tactic.Omega

/-!
# Final (1,1) reset integration for the TM63 root score

Agent 48's arbitrary-parameter M1OneQ4Prefix source theorem discharges the
last reset-prefix premise in the root-connected first-reset attainment
interface.  The only remaining machine-specific premise is the middle/last
Coq itinerary after the first Rst1' reset.  This module does not claim that
itinerary or an unconditional BB(6) score.
-/

namespace BB6Coverage.Agent42FinalResetIntegration

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent8Rst1PrimeRoot
open BB6Coverage.Agent48FinalRst1
open BB6ChampionArithmetic

/-- The final (m,n)=(1,1) reset prefix is now a theorem at the exact
arithmetic parameters of the published TM63 candidate. -/
theorem tm63_final_reset_prefix_source (h : Int) :
    run tm2 (resetPrefixCost 1 1 tm63FinalA tm63FinalB)
      (s1Config tm63Length2 1 1 tm63FinalA 0 tm63FinalB h) =
      some (s0Config (markerWord 0 ++ d0 ++ binDec tm63Length2 0 ++ lh)
        (tm63FinalA+tm63FinalB+resetDelta 1)
        (2^tm63FinalB-1) 0 (h+5+3*tm63FinalB)) := by
  have hL : 0 < tm63Length2 := by
    unfold tm63Length2 tm63Length1
    omega
  have hrun := m1One_q4_reset_prefix_source
    tm63Length2 tm63FinalA tm63FinalB h hL
  simpa [s1Config, resetDelta] using hrun

/-- Root-connected attained-score theorem with the final reset supplied
internally.  The sole remaining premise is the exact original-source
middle/last itinerary from the post-first-reset state to the final S1 input. -/
theorem tm63_attainable_after_first_reset_source
    (h : Int)
    (hstage :
      run tm2 tm63AfterFirstResetSteps
        (s1Config tm63Length1 tm63Index1 2
          tm63FirstSection.right 0 (nextRight tm63FirstSection.right)
          tm63AfterFirstResetHead) =
        some (s1Config tm63Length2 1 1 tm63FinalA 0 tm63FinalB h)) :
    Attainable proposedChampionScore := by
  exact tm63_attainable_after_first_reset_q4 h hstage
    (tm63_final_reset_prefix_source h)

#print axioms tm63_final_reset_prefix_source
#print axioms tm63_attainable_after_first_reset_source

end BB6Coverage.Agent42FinalResetIntegration
