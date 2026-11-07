import CResidualMass2000
import CResidualMass10000
import HighEvenRightC23FullForcedResidual
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent4CResidualIntegration

open BB6.Agent4CResidualMass2000
open BB6.Agent4CResidualMass10000
open BB6.Agent3FullForcedResidual

/-- A true exact mixed-root decision for a low stopping target implies
    source reachability, hence its weighted mass exceeds 2000. -/
theorem low_root_requires_mass_gt_2000 (m : Nat)
    (hroot : BB6.Agent3ValSix.valSixMixedRootDecision 1
      (2^(2*m+3)-(3*m+4)) = true) :
    2000 < BB6.Agent4MassBounds.lowRawMass m := by
  have hc : BB6.Agent3.CReach 1 (lowStopTargetY m) := by
    simpa [lowStopTargetY] using
      (BB6.Agent3ValSix.valSixMixedRootDecision_iff 1
        (lowStopTargetY m)).mp hroot
  have hr : BB6.Agent11Mass.SectionReach 1 (lowStopTargetY m) := by
    simpa [BB6.Agent3.CReach, BB6.Agent11Mass.SectionReach] using hc
  exact low_reach_implies_mass_gt_2000 m hr

/-- A true exact mixed-root decision for a high stopping target implies
    source reachability, hence its weighted mass exceeds 2000. -/
theorem high_root_requires_mass_gt_2000 (j m : Nat)
    (hroot : BB6.Agent3ValSix.valSixMixedRootDecision
      (highTargetX j) (highTargetY j m) = true) :
    2000 < BB6.Agent4MassBounds.highRawMass j m := by
  have hc : BB6.Agent3.CReach (highTargetX j) (highTargetY j m) :=
    (BB6.Agent3ValSix.valSixMixedRootDecision_iff
      (highTargetX j) (highTargetY j m)).mp hroot
  have hr : BB6.Agent11Mass.SectionReach
      (highStopTarget j m).1 (highStopTarget j m).2 := by
    simpa [BB6.Agent3.CReach, BB6.Agent11Mass.SectionReach,
      highTargetX, highTargetY, highStopTarget] using hc
  exact high_reach_implies_mass_gt_2000 j m hr

/-- Any genuine original Machine C halt must use a low or high stopping
    target whose weighted mass exceeds 2000. This composes the exact
    original-source halt equivalence with the finite mass exclusion. -/
theorem machineC_halt_requires_target_mass_gt_2000 :
    BB6.CReachBridge.RunHalts →
      (∃ m, BB6.Agent20C70.lowAllowedC70 m ∧
        2000 < BB6.Agent4MassBounds.lowRawMass m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4)) = true) ∨
      (∃ j m, highAllowedC23WithEvenRightFullForcedBool j m = true ∧
        2000 < BB6.Agent4MassBounds.highRawMass j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision
          (highTargetX j) (highTargetY j m) = true) := by
  intro hhalt
  rcases (blank_halts_iff_c23_even_right_full_forced_bool.mp hhalt) with
    hlow | ⟨j,m,hallowed,hroot⟩
  · rcases hlow with ⟨m,hallowed,hroot⟩
    exact Or.inl ⟨m,hallowed,low_root_requires_mass_gt_2000 m hroot,hroot⟩
  · exact Or.inr ⟨j,m,hallowed,high_root_requires_mass_gt_2000 j m hroot,hroot⟩

/-- The low stopping family cannot halt for m<4. -/
theorem low_root_requires_m_ge4 (m : Nat)
    (hroot : BB6.Agent3ValSix.valSixMixedRootDecision 1
      (2^(2*m+3)-(3*m+4)) = true) :
    4 ≤ m := by
  have hmass := low_root_requires_mass_gt_2000 m hroot
  by_cases hm : 4 ≤ m
  · exact hm
  · have hcases : m=0 ∨ m=1 ∨ m=2 ∨ m=3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · rw [BB6.Agent4MassBounds.low_raw_mass_m0] at hmass
      omega
    · rw [BB6.Agent4MassBounds.low_raw_mass_m1] at hmass
      omega
    · rw [BB6.Agent4MassBounds.low_raw_mass_m2] at hmass
      omega
    · rw [BB6.Agent4MassBounds.low_raw_mass_m3] at hmass
      omega

/-- Exact surviving parameter tail forced by the mass-2000 theorem. -/
theorem high_root_requires_parameter_tail (j m : Nat)
    (hroot : BB6.Agent3ValSix.valSixMixedRootDecision
      (highTargetX j) (highTargetY j m) = true) :
    4 ≤ m ∨ (m=0 ∧ 248≤j) ∨ (m=1 ∧ 60≤j) ∨
      (m=2 ∧ 13≤j) ∨ (m=3 ∧ 1≤j) := by
  have hmass := high_root_requires_mass_gt_2000 j m hroot
  by_cases hm : 4 ≤ m
  · exact Or.inl hm
  · have hcases : m=0 ∨ m=1 ∨ m=2 ∨ m=3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · rw [BB6.Agent4MassBounds.high_raw_mass_m0] at hmass
      exact Or.inr (Or.inl ⟨rfl, by omega⟩)
    · rw [BB6.Agent4MassBounds.high_raw_mass_m1] at hmass
      exact Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))
    · rw [BB6.Agent4MassBounds.high_raw_mass_m2] at hmass
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))
    · rw [BB6.Agent4MassBounds.high_raw_mass_m3] at hmass
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, by omega⟩)))


/-- The stronger one-pass source exclusion: every low-family root halt
    candidate has raw mass strictly greater than 10,000. -/
theorem low_root_requires_mass_gt_10000 (m : Nat)
    (hroot : BB6.Agent3ValSix.valSixMixedRootDecision 1
      (2^(2*m+3)-(3*m+4)) = true) :
    10000 < BB6.Agent4MassBounds.lowRawMass m := by
  have hc : BB6.Agent3.CReach 1 (lowStopTargetY m) := by
    simpa [lowStopTargetY] using
      (BB6.Agent3ValSix.valSixMixedRootDecision_iff 1
        (lowStopTargetY m)).mp hroot
  have hr : BB6.Agent11Mass.SectionReach 1 (lowStopTargetY m) := by
    simpa [BB6.Agent3.CReach, BB6.Agent11Mass.SectionReach] using hc
  exact BB6.Agent4CResidualMass10000.low_reach_implies_mass_gt_10000 m hr

/-- The stronger one-pass source exclusion: every high-family root halt
    candidate has raw mass strictly greater than 10,000. -/
theorem high_root_requires_mass_gt_10000 (j m : Nat)
    (hroot : BB6.Agent3ValSix.valSixMixedRootDecision
      (highTargetX j) (highTargetY j m) = true) :
    10000 < BB6.Agent4MassBounds.highRawMass j m := by
  have hc : BB6.Agent3.CReach (highTargetX j) (highTargetY j m) :=
    (BB6.Agent3ValSix.valSixMixedRootDecision_iff
      (highTargetX j) (highTargetY j m)).mp hroot
  have hr : BB6.Agent11Mass.SectionReach
      (highStopTarget j m).1 (highStopTarget j m).2 := by
    simpa [BB6.Agent3.CReach, BB6.Agent11Mass.SectionReach,
      highTargetX, highTargetY, highStopTarget] using hc
  exact BB6.Agent4CResidualMass10000.high_reach_implies_mass_gt_10000 j m hr

/-- Any genuine original Machine C halt must use a low or high stopping
    target whose weighted mass exceeds 10,000. -/
theorem machineC_halt_requires_target_mass_gt_10000 :
    BB6.CReachBridge.RunHalts →
      (∃ m, BB6.Agent20C70.lowAllowedC70 m ∧
        10000 < BB6.Agent4MassBounds.lowRawMass m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4)) = true) ∨
      (∃ j m, highAllowedC23WithEvenRightFullForcedBool j m = true ∧
        10000 < BB6.Agent4MassBounds.highRawMass j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision
          (highTargetX j) (highTargetY j m) = true) := by
  intro hhalt
  rcases (blank_halts_iff_c23_even_right_full_forced_bool.mp hhalt) with
    hlow | ⟨j,m,hallowed,hroot⟩
  · rcases hlow with ⟨m,hallowed,hroot⟩
    exact Or.inl ⟨m,hallowed,low_root_requires_mass_gt_10000 m hroot,hroot⟩
  · exact Or.inr ⟨j,m,hallowed,high_root_requires_mass_gt_10000 j m hroot,hroot⟩

/-- Every low stopping-family halt candidate must lie in the m≥5 tail. -/
theorem low_root_requires_m_ge5 (m : Nat)
    (hroot : BB6.Agent3ValSix.valSixMixedRootDecision 1
      (2^(2*m+3)-(3*m+4)) = true) :
    5 ≤ m := by
  have hmass := low_root_requires_mass_gt_10000 m hroot
  by_cases hm : 5 ≤ m
  · exact hm
  · have hcases : m=0 ∨ m=1 ∨ m=2 ∨ m=3 ∨ m=4 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · rw [BB6.Agent4MassBounds.low_raw_mass_m0] at hmass
      omega
    · rw [BB6.Agent4MassBounds.low_raw_mass_m1] at hmass
      omega
    · rw [BB6.Agent4MassBounds.low_raw_mass_m2] at hmass
      omega
    · rw [BB6.Agent4MassBounds.low_raw_mass_m3] at hmass
      omega
    · have hrow : BB6.Agent4MassBounds.lowRawMass 4 = 4065 := by
        rw [BB6.Agent4MassBounds.lowRawMass_eq]
      rw [hrow] at hmass
      omega

/-- Exact high-row parameter tails forced by the mass-10,000 theorem. -/
theorem high_root_requires_parameter_tail_10000 (j m : Nat)
    (hroot : BB6.Agent3ValSix.valSixMixedRootDecision
      (highTargetX j) (highTargetY j m) = true) :
    5 ≤ m ∨ (m=0 ∧ 1248≤j) ∨ (m=1 ∧ 310≤j) ∨
      (m=2 ∧ 76≤j) ∨ (m=3 ∧ 17≤j) ∨ (m=4 ∧ 2≤j) := by
  have hmass := high_root_requires_mass_gt_10000 j m hroot
  by_cases hm : 5 ≤ m
  · exact Or.inl hm
  · have hcases : m=0 ∨ m=1 ∨ m=2 ∨ m=3 ∨ m=4 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · rw [BB6.Agent4MassBounds.high_raw_mass_m0] at hmass
      exact Or.inr (Or.inl ⟨rfl, by omega⟩)
    · rw [BB6.Agent4MassBounds.high_raw_mass_m1] at hmass
      exact Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))
    · rw [BB6.Agent4MassBounds.high_raw_mass_m2] at hmass
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))
    · rw [BB6.Agent4MassBounds.high_raw_mass_m3] at hmass
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))))
    · have hrow : BB6.Agent4MassBounds.highRawMass j 4 = 2048*j+6113 := by
        rw [BB6.Agent4MassBounds.highRawMass_eq]
        have hp : 2^(2*4+3) = 2048 := by decide
        rw [hp]
        omega
      rw [hrow] at hmass
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, by omega⟩))))

#print axioms low_root_requires_mass_gt_2000
#print axioms high_root_requires_mass_gt_2000
#print axioms machineC_halt_requires_target_mass_gt_2000
#print axioms low_root_requires_m_ge4
#print axioms high_root_requires_parameter_tail
#print axioms low_root_requires_mass_gt_10000
#print axioms high_root_requires_mass_gt_10000
#print axioms machineC_halt_requires_target_mass_gt_10000
#print axioms low_root_requires_m_ge5
#print axioms high_root_requires_parameter_tail_10000

end BB6.Agent4CResidualIntegration
