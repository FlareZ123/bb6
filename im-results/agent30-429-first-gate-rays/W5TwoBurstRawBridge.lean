import W5TwoBurst
import FirstGateRaw
import Lean.Elab.Tactic.Omega

namespace BB429TwoBurstRaw
open BB429TwoBurst BB429FirstGateRays BB429FirstGateRaw
open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429High3Ladder

def lowU (t : Nat) : Nat := 24*qTwo t-3
def lowW (t : Nat) : Nat := 8*qTwo t-42-12*t

theorem low_geometry (t : Nat) :
    branchU 3 (4*t+7) = lowU t ∧
    branchShift 3 (4*t+7) + lowW t = 4*kTwo t+17 := by
  have hu := branchU_closed 3 (4*t+7)
  have hs := branchShift_closed 3 (4*t+7)
  have hp := (pow_two t).2
  have hk := kTwo_formula t
  have hq := q_bound t
  rw [hp] at hu hs
  dsimp [lowU,lowW]
  constructor <;> omega

theorem low_budget (t : Nat) :
    branchShift 3 (4*t+7) ≤ 4*kTwo t+17 := by
  have h := (low_geometry t).2
  omega

theorem low_remainder (t : Nat) :
    4*kTwo t+17 - branchShift 3 (4*t+7) = lowW t := by
  have h := (low_geometry t).2
  omega

/-- The exact one-step low-even original-machine rule is the sole remaining
    explicit hypothesis. Any certified physical proof of this one low-J ray
    composes into a full raw six-state halting family. -/
theorem raw_two_burst_of_low_ray (t N : Nat)
    (hrow : run target429 N (jConfig (lowU t) (lowW t)) =
      some (shiftConfig (9-2*(lowU t : Int))
        (jConfig 11 (anc 11 (4*t+5))))) :
    run target429
      (branchCostSum 3 (4*t+7) + N +
        (branchCostSum 11 (4*t+5) + branchCost (branchU 11 (4*t+5))))
      (jConfig 3 (4*kTwo t+17)) = none := by
  have hg := low_geometry t
  have hfirst := j_high3_ladder 3 (4*kTwo t+17) (4*t+7) 0 (low_budget t)
  have hfinal := raw_fatal_anc 11 (4*t+5) (by omega)
  have hmid :
      run target429 N
        (shiftConfig (branchShift 3 (4*t+7) : Int)
          (jConfig (lowU t) (lowW t))) =
      some (shiftConfig ((branchShift 3 (4*t+7) : Int) + (9-2*(lowU t:Int)))
        (jConfig 11 (anc 11 (4*t+5)))) := by
    rw [run_shiftConfig, hrow]
    simp only [Option.map_some]
    rw [shiftConfig_comp]
  have htwo :
      run target429
        (N+(branchCostSum 11 (4*t+5) + branchCost (branchU 11 (4*t+5))))
        (shiftConfig (branchShift 3 (4*t+7) : Int)
          (jConfig (lowU t) (lowW t))) = none := by
    rw [run_add', hmid]
    simp only [Option.bind_some]
    rw [run_shiftConfig,hfinal]
    rfl
  have hfirst' : run target429 (branchCostSum 3 (4*t+7))
     (jConfig 3 (4*kTwo t+17)) =
     some (shiftConfig (branchShift 3 (4*t+7) : Int)
       (jConfig (lowU t) (lowW t))) := by
    simpa [show (0:Int)+(branchShift 3 (4*t+7):Int) =
      (branchShift 3 (4*t+7):Int) by omega,
      shiftConfig, hg.1, low_remainder t] using hfirst
  have htime : branchCostSum 3 (4*t+7) + N +
    (branchCostSum 11 (4*t+5) + branchCost (branchU 11 (4*t+5))) =
    branchCostSum 3 (4*t+7) +
      (N+(branchCostSum 11 (4*t+5) + branchCost (branchU 11 (4*t+5)))) := by omega
  rw [htime,run_add',hfirst']
  simpa using htwo

#print axioms low_geometry
#print axioms raw_two_burst_of_low_ray
end BB429TwoBurstRaw
