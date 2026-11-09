import JChartTwo
import Low3Physical
import Lean.Elab.Tactic.Omega

namespace BB429JLow3Chart

open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical
open BB429PhysicalBridge BB429JuncCanonical BB429JChartTwo
open BB429Low3Physical

/-- A fully literal original-machine return at every translated low3
    canonical J starting configuration. Entire infinite physical tape,
    absolute head, and primitive runtime are specified. -/
theorem j_low3_chart_shift (v : Nat) (d : Int) :
    run target429 (4*v*v+22*v+54)
      (shiftConfig d (jConfig (v+2) (2*v+1))) =
      some (shiftConfig (d-((2*v+6 : Nat) : Int))
        (jConfig 0 (4*v+10))) := by
  obtain ⟨c,hr,hrep,hhead⟩ := low3_raw_head v
  have hc := represented_junc_eq_translatedJ 0 (4*v+10) c hrep
  rw [hhead] at hc
  have hh := translatedJ_eq_shift 0 (4*v+10)
     (-((2*v+6 : Nat) : Int))
  have heq := hc.trans hh
  have hraw : run target429 (4*v*v+22*v+54)
      (jConfig (v+2) (2*v+1)) =
      some (shiftConfig (-((2*v+6 : Nat) : Int))
        (jConfig 0 (4*v+10))) := by
    exact hr.trans (congrArg some heq)
  rw [run_shiftConfig, hraw]
  simp only [Option.map_some]
  rw [shiftConfig_comp]
  rw [show d+(-((2*v+6 : Nat) : Int)) =
      d-((2*v+6 : Nat) : Int) by omega]

/-- Same exact transition in standard u coordinates. -/
theorem j_low3_chart_u (u : Nat) (d : Int) (hu : 2 ≤ u) :
    run target429 (4*u*u+6*u+26)
      (shiftConfig d (jConfig u (2*u-3))) =
      some (shiftConfig (d-((2*u+2 : Nat) : Int))
        (jConfig 0 (4*u+2))) := by
  have hv : u-2+2=u := by omega
  have hw : 2*(u-2)+1=2*u-3 := by omega
  have ht : 4*(u-2)*(u-2)+22*(u-2)+54 =
      4*u*u+6*u+26 := by omega
  have hd : 2*(u-2)+6=2*u+2 := by omega
  have hJ : 4*(u-2)+10=4*u+2 := by omega
  simpa only [hv,hw,ht,hd,hJ] using j_low3_chart_shift (u-2) d

#print axioms j_low3_chart_shift
#print axioms j_low3_chart_u
end BB429JLow3Chart
