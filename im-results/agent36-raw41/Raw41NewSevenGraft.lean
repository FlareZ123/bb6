import Raw41NewSixGraft
import Raw41New125Closed

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Raw41
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31FourHoleRoster BB6.Agent50TNFPilot

/-- The sole non-FAR leaf of this cylinder is an exact first query at 1423,
    after which no unassigned nonhalting transitions can remain. -/
def removeLate125 (xs : List (List Move × PartialMachine)) :=
  xs.filter fun e => !(sameTable e.2 Raw41New125_p)

theorem removeLate125_sound (B : Nat) (hB : 1500 ≤ B) (m : Machine)
    (xs : List (List Move × PartialMachine))
    (h : WeightedBound B m ∨ ∃ e ∈ xs, TNFQuotientCompatible e.2 m) :
    WeightedBound B m ∨ ∃ e ∈ removeLate125 xs, TNFQuotientCompatible e.2 m := by
  rcases h with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases h125 : sameTable e.2 Raw41New125_p = true
    · exact Or.inl (fun k d hk hd =>
        Nat.le_trans (Raw41New125_bound m ((sameTable_sound h125) ▸ hq) k d hk hd) hB)
    · exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [removeLate125,h125]⟩,hq⟩

def afterNewSeven := removeLate125 afterNewSix

theorem new125_unique :
    (canonicalRemaining.filter fun e => sameTable e.2 Raw41New125_p).length = 1 := by decide +kernel
theorem afterNewSeven_count : afterNewSeven.length = 146 := by decide +kernel
theorem afterNewSeven_sound : ∀ m, TNFQuotientCompatible parent m →
    WeightedBound 1500 m ∨ ∃ e ∈ afterNewSeven, TNFQuotientCompatible e.2 m := by
  intro m hm
  apply removeLate125_sound 1500 (by decide)
  rcases afterNewSix_sound m hm with hb | h
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · exact Or.inr h

noncomputable def globalNewSeven := removeLate125 globalNewSix
theorem globalNewSeven_count : globalNewSeven.length = 222 := by decide +kernel
theorem globalNewSeven_sound : ∀ m, compatible root m →
    WeightedBound 7014 m ∨ ∃ e ∈ globalNewSeven, TNFQuotientCompatible e.2 m := by
  intro m hm
  exact removeLate125_sound 7014 (by decide) m globalNewSix (globalNewSix_sound m hm)

theorem exact_at_target_newSeven (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ globalNewSeven, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB globalNewSeven_sound hLeaves champ

#print axioms removeLate125_sound
#print axioms new125_unique
#print axioms afterNewSeven_count
#print axioms afterNewSeven_sound
#print axioms globalNewSeven_count
#print axioms globalNewSeven_sound
#print axioms exact_at_target_newSeven
end BB6.Agent47Raw41
