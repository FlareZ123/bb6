import JuncCanonical
import High0Physical
import High1Physical
import High3Ladder
import Lean.Elab.Tactic.Omega

namespace BB429JChartTwo

open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical
open BB429PhysicalBridge BB429JuncCanonical BB429High3Ladder
open BB429FinishScanEDelta

/-- The exact synthetic canonical J configuration at arbitrary head offset
    is precisely the original machine's existing shiftConfig operator. -/
theorem translatedJ_eq_shift (u w : Nat) (d : Int) :
    translatedJ u w d = shiftConfig d (jConfig u w) := by
  simp [translatedJ, shiftConfig, jConfig]

/-- A full original-machine J-chart return for the formerly unresolved
    w=2u boundary. This is literal whole-configuration equality. -/
theorem j_high0_chart (u : Nat) :
    run target429 (4*u*u+28*u+110) (jConfig u (2*u)) =
      some (shiftConfig (-((2*u+6 : Nat) : Int))
        (jConfig 0 (4*u+12))) := by
  obtain ⟨c,hRun,hRep,hHead⟩ :=
    BB429High0Physical.j_high0_to_junc_raw u
  have hc := represented_junc_eq_translatedJ 0 (4*u+12) c hRep
  rw [hHead] at hc
  have hh := translatedJ_eq_shift 0 (4*u+12)
     (-((2*u+6 : Nat) : Int))
  have hcfg := hc.trans hh
  change run target429 (4*u*u+28*u+110) (jConfig u (2*u)) =
    some (shiftConfig (-((2*u+6 : Nat) : Int))
      (jConfig 0 (4*u+12)))
  exact hRun.trans (congrArg some hcfg)

/-- A full original-machine J-chart return for the formerly unresolved
    w=2u+1 boundary. The entire infinite tape is exactly translated. -/
theorem j_high1_chart (u : Nat) :
    run target429 (4*u*u+28*u+306) (jConfig u (2*u+1)) =
      some (shiftConfig (6-2*(u:Int))
        (jConfig 11 (4*u+2))) := by
  obtain ⟨c,hRun,hRep,hHead⟩ :=
    BB429High1Physical.j_high1_to_junc_raw u
  have hc := represented_junc_eq_translatedJ 11 (4*u+2) c hRep
  rw [hHead] at hc
  have hh := translatedJ_eq_shift 11 (4*u+2) (6-2*(u:Int))
  have hcfg := hc.trans hh
  change run target429 (4*u*u+28*u+306) (jConfig u (2*u+1)) =
    some (shiftConfig (6-2*(u:Int))
      (jConfig 11 (4*u+2)))
  exact hRun.trans (congrArg some hcfg)

/-- Translate the high-zero branch to any original physical head offset. -/
theorem j_high0_chart_shift (u : Nat) (d : Int) :
    run target429 (4*u*u+28*u+110)
      (shiftConfig d (jConfig u (2*u))) =
      some (shiftConfig (d-((2*u+6 : Nat) : Int))
        (jConfig 0 (4*u+12))) := by
  rw [run_shiftConfig, j_high0_chart]
  simp only [Option.map_some]
  rw [shiftConfig_comp]
  rw [show d + (-((2*u+6 : Nat) : Int)) =
    d-((2*u+6 : Nat) : Int) by omega]

/-- Translate the high-one branch to any original physical head offset. -/
theorem j_high1_chart_shift (u : Nat) (d : Int) :
    run target429 (4*u*u+28*u+306)
      (shiftConfig d (jConfig u (2*u+1))) =
      some (shiftConfig (d+6-2*(u:Int))
        (jConfig 11 (4*u+2))) := by
  rw [run_shiftConfig, j_high1_chart]
  simp only [Option.map_some]
  rw [shiftConfig_comp]
  rw [show d + (6-2*(u:Int)) = d+6-2*(u:Int) by omega]

#print axioms j_high0_chart
#print axioms j_high1_chart
#print axioms j_high0_chart_shift
#print axioms j_high1_chart_shift

end BB429JChartTwo
