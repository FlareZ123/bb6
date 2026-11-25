import FiveHoleRoster
import AllTwelveRoster
import NewFiveRoster
import RosterCoverComposition

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Combined106

open BB6Coverage
open BB6.Agent13BlankDelay

/-- The union of three source-audited, pairwise-disjoint first-one cuts:
    raw66/70/80 at 395; raw86/87/88/91/92/93/97/98/100/101/102/104
    at 7014; and raw68/72/82 at 7014. -/
def covered (p : PartialMachine) : Bool :=
  (BB6.Agent10FiveHoleRoster.covered p ||
    BB6.Agent10TwelveRoster.covered p) ||
    BB6.Agent10NewFiveRoster.covered p

noncomputable def reducedRoster :=
  BB6.Agent31FourHoleRoster.remainingRootRoster.filter fun e => !(covered e.2)

theorem five_hole_count :
    (BB6.Agent31FourHoleRoster.remainingRootRoster.filter
      fun e => BB6.Agent10FiveHoleRoster.covered e.2).length = 3 := by
  decide

theorem twelve_count :
    (BB6.Agent31FourHoleRoster.remainingRootRoster.filter
      fun e => BB6.Agent10TwelveRoster.covered e.2).length = 12 := by
  decide

theorem new_five_count :
    (BB6.Agent31FourHoleRoster.remainingRootRoster.filter
      fun e => BB6.Agent10NewFiveRoster.covered e.2).length = 3 := by
  decide

theorem five_twelve_disjoint :
    (BB6.Agent31FourHoleRoster.remainingRootRoster.filter
      fun e => BB6.Agent10FiveHoleRoster.covered e.2 &&
        BB6.Agent10TwelveRoster.covered e.2).length = 0 := by
  decide

theorem five_new_disjoint :
    (BB6.Agent31FourHoleRoster.remainingRootRoster.filter
      fun e => BB6.Agent10FiveHoleRoster.covered e.2 &&
        BB6.Agent10NewFiveRoster.covered e.2).length = 0 := by
  decide

theorem twelve_new_disjoint :
    (BB6.Agent31FourHoleRoster.remainingRootRoster.filter
      fun e => BB6.Agent10TwelveRoster.covered e.2 &&
        BB6.Agent10NewFiveRoster.covered e.2).length = 0 := by
  decide

theorem covered_count :
    (BB6.Agent31FourHoleRoster.remainingRootRoster.filter
      fun e => covered e.2).length = 18 := by
  decide

/-- The three accepted groups close eighteen distinct cylinders, leaving
    exactly 106 of the original 124 residual cylinders at weighted bound 7014. -/
theorem reduced_count : reducedRoster.length = 106 := by
  decide

theorem covered_sound (p : PartialMachine) (h : covered p = true)
    (m : Machine) (hm : compatible p m) : WeightedBound 7014 m := by
  simp only [covered, Bool.or_eq_true] at h
  rcases h with hFiveOrTwelve | hNew
  · rcases hFiveOrTwelve with hFive | hTwelve
    · have hb := BB6.Agent10FiveHoleRoster.covered_sound p hFive m hm
      intro k d hk hd
      exact Nat.le_trans (hb k d hk hd) (by decide)
    · exact BB6.Agent10TwelveRoster.covered_sound p hTwelve m hm
  · exact BB6.Agent10NewFiveRoster.covered_sound p hNew m hm

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

theorem cover_of_reduced_roster
    (hLeaves : ∀ e ∈ reducedRoster, Cover (WeightedBound 7014) e.2) :
    Cover (WeightedBound 7014) BB6.Agent50TNFPilot.root :=
  BB6.Agent13RosterComposition.cover_of_roster_dichotomy reduced_sound hLeaves

noncomputable def tnf_certificate_of_reduced_roster
    (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ reducedRoster, Cover (WeightedBound 7014) e.2) :
    WeightedTNFCertificate B BB6.CoverageAdapter.firstOneCylinder 2 :=
  BB6.Agent13RosterComposition.tnf_certificate_of_roster_dichotomy
    hB reduced_sound hLeaves

theorem exact_from_reduced_roster (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ reducedRoster, Cover (WeightedBound 7014) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  BB6.Agent13RosterComposition.exact_from_roster_dichotomy
    (by decide) hB reduced_sound hLeaves champ

#print axioms five_hole_count
#print axioms twelve_count
#print axioms new_five_count
#print axioms five_twelve_disjoint
#print axioms five_new_disjoint
#print axioms twelve_new_disjoint
#print axioms covered_count
#print axioms reduced_count
#print axioms covered_sound
#print axioms reduced_sound
#print axioms cover_of_reduced_roster
#print axioms exact_from_reduced_roster

end BB6.Agent47Combined106
