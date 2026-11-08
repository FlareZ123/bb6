import JChartThree
import High3Ladder
import Lean.Elab.Tactic.Omega

namespace BB429JCompleteChart

open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical
open BB429High3Ladder BB429JChartTwo BB429JChartThree

/-- Primitive duration of the exact J-chart exit. The domain restriction
    w+1≥2u is carried by the main theorem. -/
def chartStepTime (u w : Nat) : Nat :=
  if w+1=2*u then 4*u*u+10*u+27
  else if w=2*u then 4*u*u+28*u+110
  else if w=2*u+1 then 4*u*u+28*u+306
  else if w=2*u+2 then 4*u*u+44*u+204
  else 4*u*u+10*u+27

/-- Entire physical successor configuration, including its absolute head
    and each cell of the two-sided infinite tape. None means actual halt. -/
def chartStepResult (u w : Nat) (d : Int) : Option Config :=
  if w+1=2*u then none
  else if w=2*u then
    some (shiftConfig (d-((2*u+6 : Nat) : Int)) (jConfig 0 (4*u+12)))
  else if w=2*u+1 then
    some (shiftConfig (d+6-2*(u:Int)) (jConfig 11 (4*u+2)))
  else if w=2*u+2 then
    some (shiftConfig (d-((2*u+10 : Nat) : Int)) (jConfig 0 (4*u+18)))
  else some (shiftConfig (d+(2*(u:Int)+3))
       (jConfig (2*u+3) (w-(2*u+3))))

/-- Full original-machine chart classifier on the whole domain w+1≥2u.
    Every possible parameter satisfies exactly one of the five branches:
    fatal boundary, high-zero, high-one, high-two, or generic high-three. -/
theorem chartStep_complete (u w : Nat) (d : Int)
    (hw : 2*u ≤ w+1) :
    run target429 (chartStepTime u w) (shiftConfig d (jConfig u w)) =
      chartStepResult u w d := by
  by_cases hF : w+1=2*u
  · have hraw : run target429 (4*u*u+10*u+27) (jConfig u w) = none := by
      simpa [jConfig] using BB429JFirstBranch.j_fatal_branch u w hF
    simp [chartStepTime, chartStepResult, hF, run_shiftConfig, hraw]
  · by_cases h0 : w=2*u
    · subst w
      have hf0 : 2*u+1 ≠ 2*u := by omega
      simpa [chartStepTime,chartStepResult,hf0] using
        (j_high0_chart_shift u d)
    · by_cases h1 : w=2*u+1
      · subst w
        have hf1 : 2*u+1+1 ≠ 2*u := by omega
        have hn0 : 2*u+1 ≠ 2*u := by omega
        simpa [chartStepTime,chartStepResult,hf1,hn0] using
          (j_high1_chart_shift u d)
      · by_cases h2 : w=2*u+2
        · subst w
          have hf2 : 2*u+2+1 ≠ 2*u := by omega
          have hn0 : 2*u+2 ≠ 2*u := by omega
          have hn1 : 2*u+2 ≠ 2*u+1 := by omega
          simpa [chartStepTime,chartStepResult,hf2,hn0,hn1] using
            (j_high2_chart_shift u d)
        · have h3 : 2*u+3 ≤ w := by omega
          simpa [chartStepTime,chartStepResult,hF,h0,h1,h2] using
            (j_first_branch_shift u w d h3)

#print axioms chartStep_complete
end BB429JCompleteChart
