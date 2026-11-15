import TM63RootQ4Attainable
import M1OneQ4Prefix
import Lean.Elab.Tactic.Omega

/-!
# Eliminate the final-reset premise from the TM63 attained-score theorem

The generic root-attainability theorem previously assumed both the remaining
root itinerary and a separate final (m,n)=(1,1) reset-prefix run.  The
source-level theorem `m1One_q4_reset_prefix_source` proves that reset for
all positive lengths and arbitrary counters, including the exact head
displacement h+5+3*b.  This adapter composes it into the exact proposed-score
theorem, leaving only the still-open original-table middle-itinerary run.
-/

namespace BB6Coverage.Agent24ChampionTime

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent48FinalRst1
open BB6ChampionArithmetic

/-- The final reset prefix is source-proved for every positive length. -/
theorem tm63Length2_pos : 0 < tm63Length2 := by
  unfold tm63Length2 tm63Length1
  omega

/-- The arbitrary-(a,b) final (m,n)=(1,1) reset source run discharges the
second machine-specific premise of the conditional champion theorem. -/
theorem tm63_final_reset_prefix_source :
    run tm2 (resetPrefixCost 1 1 tm63FinalA tm63FinalB)
      (s1Config tm63Length2 1 1 tm63FinalA 0 tm63FinalB
        (0 : Int)) =
    some (s1Config tm63Length2 0 0
      (tm63FinalA+tm63FinalB+2) (2^tm63FinalB-1) 0
      (5+3*tm63FinalB)) := by
  simpa using
    m1One_q4_reset_prefix_source tm63Length2 tm63FinalA tm63FinalB
      (0 : Int) tm63Length2_pos

/-- Exact proposed champion attainability, conditional only on the
remaining original-TM2 itinerary from the root-connected q4/drain endpoint
to the final S1(m=1,n=1) input.  The final reset prefix is no longer an
independent premise. -/
theorem tm63_attainable_at_proposedChampionScore_of_remaining_itinerary
    (h : Int)
    (hstage :
      run tm2 tm63SuffixSteps
        (s1Config 3 6 1 71 0 (2^63-1) 223) =
        some (s1Config tm63Length2 1 1 tm63FinalA 0 tm63FinalB h)) :
    Attainable proposedChampionScore := by
  have hfinalS1 :=
    m1One_q4_reset_prefix_source tm63Length2 tm63FinalA tm63FinalB h
      tm63Length2_pos
  have hfinal :
      run tm2 (resetPrefixCost 1 1 tm63FinalA tm63FinalB)
        (s1Config tm63Length2 1 1 tm63FinalA 0 tm63FinalB h) =
        some (s0Config
          (markerWord 0 ++ d0 ++ binDec tm63Length2 0 ++ lh)
          (tm63FinalA+tm63FinalB+resetDelta 1)
          (2^tm63FinalB-1) 0 (h+5+3*tm63FinalB)) := by
    simpa [s1Config, resetDelta] using hfinalS1
  exact tm63_attainable_at_proposedChampionScore h hstage hfinal

#print axioms tm63Length2_pos
#print axioms tm63_final_reset_prefix_source
#print axioms tm63_attainable_at_proposedChampionScore_of_remaining_itinerary

end BB6Coverage.Agent24ChampionTime
