import SectionFuelOriginal
import CResidualMassBounds
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent4CResidualMass2000

/-- The low stopping target for parameter m. -/
def lowStopTargetY (m : Nat) : Nat := 2^(2*m+3) - (3*m+4)

/-- The high stopping target for parameters (j,m). -/
def highStopTarget (j m : Nat) : Nat × Nat :=
  (2*j+3, 2^(2*m+2)*(j+3) - (j+3*m+5))

/-- The exact source-faithful forward root test with the half-mass fuel. -/
def massStopRoot (x y : Nat) : Bool :=
  BB6.Agent11Fuel.massStop x y ((x+2*y)/2) (some (5,1))

theorem massStopRoot_iff_sectionReach (x y : Nat) :
    massStopRoot x y = true ↔ BB6.Agent11Mass.SectionReach x y := by
  simpa [massStopRoot] using BB6.Agent11Fuel.massStopHalfFull_iff x y

/-- Kernel-computed no-hit result for all four low targets in the
    raw-mass-2000 region. -/
theorem lowNoHitAll :
    (List.range 4).all
      (fun m => decide (massStopRoot 1 (lowStopTargetY m) = false)) = true := by
  decide

/-- All 248 high targets in row m=0 are unreachable. -/
theorem highNoHitM0 :
    (List.range 248).all
      (fun j => decide (massStopRoot (2*j+3) (highStopTarget j 0).2 = false)) = true := by
  decide

/-- All 60 high targets in row m=1 are unreachable. -/
theorem highNoHitM1 :
    (List.range 60).all
      (fun j => decide (massStopRoot (2*j+3) (highStopTarget j 1).2 = false)) = true := by
  decide

/-- All 13 high targets in row m=2 are unreachable. -/
theorem highNoHitM2 :
    (List.range 13).all
      (fun j => decide (massStopRoot (2*j+3) (highStopTarget j 2).2 = false)) = true := by
  decide

/-- The only high target in row m=3 under raw mass 2000 is unreachable. -/
theorem highNoHitM3 :
    massStopRoot (highStopTarget 0 3).1 (highStopTarget 0 3).2 = false := by
  decide

/-- Every low stopping target with raw mass at most 2000 fails the
    exact blank-root reachability test. -/
theorem low_no_root_under_mass2000 (m : Nat)
    (hm : BB6.Agent4MassBounds.lowRawMass m ≤ 2000) :
    massStopRoot 1 (lowStopTargetY m) = false := by
  have hmExact := BB6.Agent4MassBounds.low_raw_mass_box_exact m hm
  have hmem : m ∈ List.range 4 := List.mem_range.mpr (by omega)
  have h := (List.all_eq_true.mp lowNoHitAll) m hmem
  exact of_decide_eq_true h

/-- Every high stopping target with raw mass at most 2000 fails the
    exact blank-root reachability test. No C70/C23/valuation filters are
    assumed, so this covers a superset of the surviving parameter families. -/
theorem high_no_root_under_mass2000 (j m : Nat)
    (hm : BB6.Agent4MassBounds.highRawMass j m ≤ 2000) :
    massStopRoot (highStopTarget j m).1 (highStopTarget j m).2 = false := by
  rcases BB6.Agent4MassBounds.high_raw_mass_box_exact j m hm with h0 | h1 | h2 | h3
  · rcases h0 with ⟨rfl,hj⟩
    have hmem : j ∈ List.range 248 := List.mem_range.mpr (by omega)
    have h := (List.all_eq_true.mp highNoHitM0) j hmem
    exact of_decide_eq_true h
  · rcases h1 with ⟨rfl,hj⟩
    have hmem : j ∈ List.range 60 := List.mem_range.mpr (by omega)
    have h := (List.all_eq_true.mp highNoHitM1) j hmem
    exact of_decide_eq_true h
  · rcases h2 with ⟨rfl,hj⟩
    have hmem : j ∈ List.range 13 := List.mem_range.mpr (by omega)
    have h := (List.all_eq_true.mp highNoHitM2) j hmem
    exact of_decide_eq_true h
  · rcases h3 with ⟨rfl,rfl⟩
    exact highNoHitM3

/-- All low stopping targets of raw mass at most 2000 are absent from
    the genuine blank-root section orbit. -/
theorem low_no_section_reach_under_mass2000 (m : Nat)
    (hm : BB6.Agent4MassBounds.lowRawMass m ≤ 2000) :
    ¬ BB6.Agent11Mass.SectionReach 1 (lowStopTargetY m) := by
  intro hr
  have htrue := (massStopRoot_iff_sectionReach 1 (lowStopTargetY m)).mpr hr
  rw [low_no_root_under_mass2000 m hm] at htrue
  cases htrue

/-- All high stopping targets of raw mass at most 2000 are absent from
    the genuine blank-root section orbit. -/
theorem high_no_section_reach_under_mass2000 (j m : Nat)
    (hm : BB6.Agent4MassBounds.highRawMass j m ≤ 2000) :
    ¬ BB6.Agent11Mass.SectionReach (highStopTarget j m).1 (highStopTarget j m).2 := by
  intro hr
  have htrue := (massStopRoot_iff_sectionReach (highStopTarget j m).1
    (highStopTarget j m).2).mpr hr
  rw [high_no_root_under_mass2000 j m hm] at htrue
  cases htrue

#print axioms massStopRoot_iff_sectionReach
#print axioms lowNoHitAll
#print axioms highNoHitM0
#print axioms highNoHitM1
#print axioms highNoHitM2
#print axioms highNoHitM3
#print axioms low_no_root_under_mass2000
#print axioms high_no_root_under_mass2000
#print axioms low_no_section_reach_under_mass2000
#print axioms high_no_section_reach_under_mass2000

end BB6.Agent4CResidualMass2000
