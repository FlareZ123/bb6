import JuncCanonical
import W5TwoBurstRawBridge
import BB429DeltaPhysicalBridge
import Lean.Elab.Tactic.Omega

namespace BB429TwoBurstT0
open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical
open BB429High3Ladder BB429JuncCanonical BB429FinishScanEDelta
open BB429DeltaPhysicalBridge BB429TwoBurst BB429TwoBurstRaw

/-- Exact finite source-level low-even row at the first two-burst
    exceptional seed. This is a computational certificate of a genuine
    54333-step zipper trace, with the entire finite-support tape checked. -/
set_option maxRecDepth 32768 in
set_option maxHeartbeats 20000000 in
theorem low_t0_source :
    runWithDelta 54333 (junc 765 0 214) =
      some (junc 11 0 1742, -1521) := by native_decide

/-- Lift the checked source zipper trace to the original actual six-state
    machine. All bi-infinite tape cells agree, not just a finite window. -/
theorem low_t0_raw :
    run target429 54333 (jConfig 765 214) =
      some (shiftConfig (-1521) (jConfig 11 1742)) := by
  have hrep : Represents (junc 765 0 214) (jConfig 765 214) := by
    simpa [jConfig] using
      (canonical_junc_rep 765 214 (0:Int))
  obtain ⟨c,hraw,href,hhead⟩ :=
    source_runWithDelta_rep 54333 (junc 765 0 214) (jConfig 765 214)
      hrep (junc 11 0 1742) (-1521) low_t0_source
  have hc := represented_junc_eq_translatedJ 11 1742 c href
  have hzero : (jConfig 765 214).head=0 := rfl
  rw [hzero] at hhead
  have htarget : c = shiftConfig (-1521) (jConfig 11 1742) := by
    rw [hhead] at hc
    simpa [translatedJ,shiftConfig,jConfig] using hc
  exact hraw.trans (congrArg some htarget)

/-- The first two-burst case is now proved to halt from a genuine
    prepared J tape of the original six-state machine, rather than
    only its arithmetic accelerator. -/
theorem raw_two_burst_t0 :
    run target429
      (branchCostSum 3 7 + 54333 +
       (branchCostSum 11 5 + branchCost (branchU 11 5)))
      (jConfig 3 (4*kTwo 0+17)) = none := by
  have hrow :
      run target429 54333 (jConfig (lowU 0) (lowW 0)) =
        some (shiftConfig (9-2*(lowU 0 : Int))
          (jConfig 11 (BB429FirstGateRays.anc 11 (4*0+5)))) := by
    simpa [lowU,lowW,qTwo,BB429FirstGateRays.anc] using low_t0_raw
  exact raw_two_burst_of_low_ray 0 54333 hrow

#print axioms low_t0_source
#print axioms low_t0_raw
#print axioms raw_two_burst_t0
end BB429TwoBurstT0
