import FiveHoleRoster
import AllTwelveRoster
import RosterCoverComposition

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Combined109

open BB6Coverage
open BB6.Agent13BlankDelay

/-- Union the three accepted 395-bound cylinders and twelve accepted
    7014-bound cylinders, without duplicating their root residuals. -/
def covered (p : PartialMachine) : Bool :=
  BB6.Agent10FiveHoleRoster.covered p ||
  BB6.Agent10TwelveRoster.covered p

/-- The combined retained frontier after all fifteen source-checked cuts. -/
noncomputable def reducedRoster :=
  BB6.Agent31FourHoleRoster.remainingRootRoster.filter fun e => !(covered e.2)

/-- The three-certificate group is exactly raw66/raw70/raw80. -/
theorem five_hole_count :
    (BB6.Agent31FourHoleRoster.remainingRootRoster.filter
      fun e => BB6.Agent10FiveHoleRoster.covered e.2).length = 3 := by
  decide

/-- The twelve-certificate group is exactly raw86/87/88/91/92/93/97/98/100/101/102/104. -/
theorem twelve_count :
    (BB6.Agent31FourHoleRoster.remainingRootRoster.filter
      fun e => BB6.Agent10TwelveRoster.covered e.2).length = 12 := by
  decide

/-- The two groups are disjoint as exact partial transition tables. -/
theorem no_overlap :
    (BB6.Agent31FourHoleRoster.remainingRootRoster.filter
      fun e => BB6.Agent10FiveHoleRoster.covered e.2 &&
        BB6.Agent10TwelveRoster.covered e.2).length = 0 := by
  decide

/-- Exactly fifteen of the original 124 residual cylinders are now closed. -/
theorem covered_count :
    (BB6.Agent31FourHoleRoster.remainingRootRoster.filter
      fun e => covered e.2).length = 15 := by
  decide

/-- The source-checked root dichotomy now has 109 residual cylinders at 7014. -/
theorem reduced_count : reducedRoster.length = 109 := by
  decide

/-- Every table matched by either source-accepted group is safe at 7014.
    The first group proves 395 and is lifted monotonically; the second proves
    7014 directly. -/
theorem covered_sound (p : PartialMachine) (h : covered p = true)
    (m : Machine) (hm : compatible p m) : WeightedBound 7014 m := by
  simp only [covered, Bool.or_eq_true] at h
  rcases h with hFive | hTwelve
  · have hb := BB6.Agent10FiveHoleRoster.covered_sound p hFive m hm
    intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) (by decide)
  · exact BB6.Agent10TwelveRoster.covered_sound p hTwelve m hm

/-- Every first-one-root completion is already bounded by 7014 or extends
    one of the 109 exact residual cylinders. -/
theorem reduced_sound (m : Machine)
    (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 7014 m ∨
      ∃ e ∈ reducedRoster, compatible e.2 m := by
  rcases BB6.Agent31FourHoleRoster.remainingRootRoster_sound_7014 m hm with
    hBound | ⟨e, he, hp⟩
  · exact Or.inl hBound
  · cases hc : covered e.2 with
    | true => exact Or.inl (covered_sound e.2 hc m hp)
    | false =>
        exact Or.inr ⟨e, List.mem_filter.mpr ⟨he, by simp [hc]⟩, hp⟩

/-- Conditional root cover once every retained cylinder has a 7014 safety
    certificate. -/
theorem cover_of_reduced_roster
    (hLeaves : ∀ e ∈ reducedRoster, Cover (WeightedBound 7014) e.2) :
    Cover (WeightedBound 7014) BB6.Agent50TNFPilot.root :=
  BB6.Agent13RosterComposition.cover_of_roster_dichotomy reduced_sound hLeaves

/-- Normalized weighted-TNF certificate from the 109 remaining obligations. -/
noncomputable def tnf_certificate_of_reduced_roster
    (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ reducedRoster, Cover (WeightedBound 7014) e.2) :
    WeightedTNFCertificate B BB6.CoverageAdapter.firstOneCylinder 2 :=
  BB6.Agent13RosterComposition.tnf_certificate_of_roster_dichotomy
    hB reduced_sound hLeaves

/-- Conditional exact BB(6): only the 109 retained safety Covers and the
    already checked champion attainment remain as premises. -/
theorem exact_from_reduced_roster (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ reducedRoster, Cover (WeightedBound 7014) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  BB6.Agent13RosterComposition.exact_from_roster_dichotomy
    (by decide) hB reduced_sound hLeaves champ

#print axioms five_hole_count
#print axioms twelve_count
#print axioms no_overlap
#print axioms covered_count
#print axioms reduced_count
#print axioms covered_sound
#print axioms reduced_sound
#print axioms cover_of_reduced_roster
#print axioms exact_from_reduced_roster

end BB6.Agent47Combined109
