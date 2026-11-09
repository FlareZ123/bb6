import CResidualMassIntegration
import CResidualMass100000
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent47C100K

open BB6.Agent4CResidualMass2000
open BB6.Agent3FullForcedResidual

/-- The original-source fixed-target oracle can be true on a low stopping
    input only when that input's weighted mass exceeds 100,000. -/
theorem low_root_mass_gt (m : Nat)
    (hroot : BB6.Agent3ValSix.valSixMixedRootDecision 1
      (2^(2*m+3)-(3*m+4)) = true) :
    100000 < BB6.Agent4MassBounds.lowRawMass m := by
  have hc : BB6.Agent3.CReach 1 (lowStopTargetY m) := by
    simpa [lowStopTargetY] using
      (BB6.Agent3ValSix.valSixMixedRootDecision_iff 1
        (lowStopTargetY m)).mp hroot
  have hr : BB6.Agent11Mass.SectionReach 1 (lowStopTargetY m) := by
    simpa [BB6.Agent3.CReach, BB6.Agent11Mass.SectionReach] using hc
  exact BB6.Agent4CResidualMass100000.low_reach_implies_mass_gt_100000 m hr

/-- The original-source fixed-target oracle can be true on a high stopping
    input only when that input's weighted mass exceeds 100,000. -/
theorem high_root_mass_gt (j m : Nat)
    (hroot : BB6.Agent3ValSix.valSixMixedRootDecision
      (highTargetX j) (highTargetY j m) = true) :
    100000 < BB6.Agent4MassBounds.highRawMass j m := by
  have hc : BB6.Agent3.CReach (highTargetX j) (highTargetY j m) :=
    (BB6.Agent3ValSix.valSixMixedRootDecision_iff
      (highTargetX j) (highTargetY j m)).mp hroot
  have hr : BB6.Agent11Mass.SectionReach
      (highStopTarget j m).1 (highStopTarget j m).2 := by
    simpa [BB6.Agent3.CReach, BB6.Agent11Mass.SectionReach,
      highTargetX, highTargetY, highStopTarget] using hc
  exact BB6.Agent4CResidualMass100000.high_reach_implies_mass_gt_100000 j m hr

/-- The original Machine C blank run halts iff a surviving low/high
    source candidate has weighted mass strictly greater than 100,000.
    This is an exact reparameterization of the source halting criterion,
    not a proof of nonhalting. -/
theorem source_halts_iff_mass100k :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent20C70.lowAllowedC70 m ∧
        100000 < BB6.Agent4MassBounds.lowRawMass m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4)) = true) ∨
      (∃ j m, highAllowedC23WithEvenRightFullForcedBool j m = true ∧
        100000 < BB6.Agent4MassBounds.highRawMass j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision
          (highTargetX j) (highTargetY j m) = true) := by
  constructor
  · intro hhalt
    rcases (blank_halts_iff_c23_even_right_full_forced_bool.mp hhalt) with
      ⟨m,hallowed,hroot⟩ | ⟨j,m,hallowed,hroot⟩
    · exact Or.inl ⟨m,hallowed,low_root_mass_gt m hroot,hroot⟩
    · exact Or.inr ⟨j,m,hallowed,high_root_mass_gt j m hroot,hroot⟩
  · intro h
    apply blank_halts_iff_c23_even_right_full_forced_bool.mpr
    rcases h with ⟨m,hallowed,_,hroot⟩ | ⟨j,m,hallowed,_,hroot⟩
    · exact Or.inl ⟨m,hallowed,hroot⟩
    · exact Or.inr ⟨j,m,hallowed,hroot⟩

/-- No authentic low stopping input can have depth less than seven. -/
theorem low_root_depth_ge7 (m : Nat)
    (hroot : BB6.Agent3ValSix.valSixMixedRootDecision 1
      (2^(2*m+3)-(3*m+4)) = true) : 7 ≤ m := by
  have hmass := low_root_mass_gt m hroot
  by_cases hm : 7 ≤ m
  · exact hm
  · have hcases : m=0 ∨ m=1 ∨ m=2 ∨ m=3 ∨
        m=4 ∨ m=5 ∨ m=6 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [BB6.Agent4MassBounds.lowRawMass_eq] at hmass

/-- Every genuine high stopping input must lie in one of the exact
    seven unbounded parameter tails below. -/
theorem high_root_parameter_tail (j m : Nat)
    (hroot : BB6.Agent3ValSix.valSixMixedRootDecision
      (highTargetX j) (highTargetY j m) = true) :
    7 ≤ m ∨
      (m=0 ∧ 12498≤j) ∨
      (m=1 ∧ 3123≤j) ∨
      (m=2 ∧ 779≤j) ∨
      (m=3 ∧ 193≤j) ∨
      (m=4 ∧ 46≤j) ∨
      (m=5 ∧ 10≤j) ∨
      (m=6 ∧ 1≤j) := by
  have hmass := high_root_mass_gt j m hroot
  by_cases hm : 7 ≤ m
  · exact Or.inl hm
  · have hcases : m=0 ∨ m=1 ∨ m=2 ∨ m=3 ∨
        m=4 ∨ m=5 ∨ m=6 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [BB6.Agent4MassBounds.high_raw_mass_m0] at hmass
      omega
    · rw [BB6.Agent4MassBounds.high_raw_mass_m1] at hmass
      omega
    · rw [BB6.Agent4MassBounds.high_raw_mass_m2] at hmass
      omega
    · rw [BB6.Agent4MassBounds.high_raw_mass_m3] at hmass
      omega
    · have hrow : BB6.Agent4MassBounds.highRawMass j 4 = 2048*j+6113 := by
        rw [BB6.Agent4MassBounds.highRawMass_eq]
        have hp : 2^(2*4+3) = 2048 := by decide
        rw [hp]
        omega
      rw [hrow] at hmass
      omega
    · have hrow : BB6.Agent4MassBounds.highRawMass j 5 = 8192*j+24539 := by
        rw [BB6.Agent4MassBounds.highRawMass_eq]
        have hp : 2^(2*5+3) = 8192 := by decide
        rw [hp]
        omega
      rw [hrow] at hmass
      omega
    · have hrow : BB6.Agent4MassBounds.highRawMass j 6 = 32768*j+98261 := by
        rw [BB6.Agent4MassBounds.highRawMass_eq]
        have hp : 2^(2*6+3) = 32768 := by decide
        rw [hp]
        omega
      rw [hrow] at hmass
      omega

#print axioms low_root_mass_gt
#print axioms high_root_mass_gt
#print axioms source_halts_iff_mass100k
#print axioms low_root_depth_ge7
#print axioms high_root_parameter_tail

end BB6.Agent47C100K
