import JChartTwo
import High2Return
import Lean.Elab.Tactic.Omega

namespace BB429JChartThree
open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical
open BB429PhysicalBridge BB429JuncCanonical BB429High3Ladder
open BB429JChartTwo BB429FinishScanEDelta

/-- Exact original #429 J(u,2u+2) whole-tape return, derived by combining
    the existing high-two physical result with canonical Junc translation. -/
theorem j_high2_chart (u : Nat) :
    run target429 (4*u*u+44*u+204) (jConfig u (2*u+2)) =
      some (shiftConfig (-((2*u+10 : Nat) : Int))
        (jConfig 0 (4*u+18))) := by
  obtain ⟨c,hRun,hRep,hHead⟩ :=
    BB429High2Return.j_high2_to_junc_raw u
  have hc := represented_junc_eq_translatedJ 0 (4*u+18) c hRep
  rw [hHead] at hc
  have hh := translatedJ_eq_shift 0 (4*u+18)
     (-((2*u+10 : Nat) : Int))
  have hcfg := hc.trans hh
  change run target429 (4*u*u+44*u+204) (jConfig u (2*u+2)) =
    some (shiftConfig (-((2*u+10 : Nat) : Int))
      (jConfig 0 (4*u+18)))
  exact hRun.trans (congrArg some hcfg)

/-- The high-two branch is also fully translation invariant. -/
theorem j_high2_chart_shift (u : Nat) (d : Int) :
    run target429 (4*u*u+44*u+204)
      (shiftConfig d (jConfig u (2*u+2))) =
      some (shiftConfig (d-((2*u+10 : Nat) : Int))
        (jConfig 0 (4*u+18))) := by
  rw [run_shiftConfig, j_high2_chart]
  simp only [Option.map_some]
  rw [shiftConfig_comp]
  rw [show d + (-((2*u+10 : Nat) : Int)) =
    d-((2*u+10 : Nat) : Int) by omega]

#print axioms j_high2_chart
#print axioms j_high2_chart_shift
end BB429JChartThree
