import Raw41NewSevenGraft
import Raw41New081Closed

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Raw41
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31FourHoleRoster BB6.Agent50TNFPilot

/-- The high-order 8-DFA nonhalting proof closes Raw41 canonical child 081. -/
def removeSMT81 (xs : List (List Move × PartialMachine)) :=
  xs.filter fun e => !(sameTable e.2 Raw41New081_p)

theorem removeSMT81_sound (B : Nat) (hB : 89 ≤ B) (m : Machine)
    (xs : List (List Move × PartialMachine))
    (h : WeightedBound B m ∨ ∃ e ∈ xs, TNFQuotientCompatible e.2 m) :
    WeightedBound B m ∨ ∃ e ∈ removeSMT81 xs, TNFQuotientCompatible e.2 m := by
  rcases h with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases h81 : sameTable e.2 Raw41New081_p = true
    · exact Or.inl (fun k d hk hd =>
        Nat.le_trans (Raw41New081_bound m ((sameTable_sound h81) ▸ hq) k d hk hd) hB)
    · exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [removeSMT81,h81]⟩,hq⟩

def afterNewEight := removeSMT81 afterNewSeven
theorem new081_unique :
    (canonicalRemaining.filter fun e => sameTable e.2 Raw41New081_p).length = 1 := by decide +kernel
theorem afterNewEight_count : afterNewEight.length = 145 := by decide +kernel
theorem afterNewEight_sound : ∀ m, TNFQuotientCompatible parent m →
    WeightedBound 1500 m ∨ ∃ e ∈ afterNewEight, TNFQuotientCompatible e.2 m := by
  intro m hm
  apply removeSMT81_sound 1500 (by decide)
  exact afterNewSeven_sound m hm

noncomputable def globalNewEight := removeSMT81 globalNewSeven
theorem globalNewEight_count : globalNewEight.length = 221 := by decide +kernel
theorem globalNewEight_sound : ∀ m, compatible root m →
    WeightedBound 7014 m ∨ ∃ e ∈ globalNewEight, TNFQuotientCompatible e.2 m := by
  intro m hm
  exact removeSMT81_sound 7014 (by decide) m globalNewSeven (globalNewSeven_sound m hm)

theorem exact_at_target_newEight (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ globalNewEight, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB globalNewEight_sound hLeaves champ

#print axioms removeSMT81_sound
#print axioms new081_unique
#print axioms afterNewEight_count
#print axioms afterNewEight_sound
#print axioms globalNewEight_count
#print axioms globalNewEight_sound
#print axioms exact_at_target_newEight
end BB6.Agent47Raw41
