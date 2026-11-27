import Raw41NewThirteenGraft
import Raw41New024Closed
import Raw41New034Closed
import Raw41New131Closed

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Raw41
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31FourHoleRoster BB6.Agent50TNFPilot

/-- Three more complete, source-checkable FAR/AutoPump five-hole
    cylinders, each distinct in the original Raw41 canonical roster. -/
def removeLastThree (xs : List (List Move × PartialMachine)) :=
  xs.filter fun e =>
    !(sameTable e.2 Raw41New024_p ||
      sameTable e.2 Raw41New034_p ||
      sameTable e.2 Raw41New131_p)

theorem removeLastThree_sound (B : Nat) (hB : 242 ≤ B) (m : Machine)
    (xs : List (List Move × PartialMachine))
    (h : WeightedBound B m ∨ ∃ e ∈ xs, TNFQuotientCompatible e.2 m) :
    WeightedBound B m ∨ ∃ e ∈ removeLastThree xs, TNFQuotientCompatible e.2 m := by
  rcases h with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases h24 : sameTable e.2 Raw41New024_p = true
    · exact Or.inl (fun k d hk hd =>
        Nat.le_trans (Raw41New024_bound m ((sameTable_sound h24) ▸ hq) k d hk hd) (by omega))
    · by_cases h34 : sameTable e.2 Raw41New034_p = true
      · exact Or.inl (fun k d hk hd =>
          Nat.le_trans (Raw41New034_bound m ((sameTable_sound h34) ▸ hq) k d hk hd) hB)
      · by_cases h131 : sameTable e.2 Raw41New131_p = true
        · exact Or.inl (fun k d hk hd =>
            Nat.le_trans (Raw41New131_bound m ((sameTable_sound h131) ▸ hq) k d hk hd) (by omega))
        · exact Or.inr ⟨e,List.mem_filter.mpr
            ⟨he, by simp [removeLastThree, h24, h34, h131]⟩,hq⟩

def afterNewSixteen := removeLastThree afterNewThirteen
theorem new024_unique :
    (canonicalRemaining.filter fun e => sameTable e.2 Raw41New024_p).length = 1 := by decide +kernel
theorem new034_unique :
    (canonicalRemaining.filter fun e => sameTable e.2 Raw41New034_p).length = 1 := by decide +kernel
theorem new131_unique :
    (canonicalRemaining.filter fun e => sameTable e.2 Raw41New131_p).length = 1 := by decide +kernel
theorem afterNewSixteen_count : afterNewSixteen.length = 137 := by decide +kernel

theorem afterNewSixteen_sound : ∀ m, TNFQuotientCompatible parent m →
    WeightedBound 1500 m ∨ ∃ e ∈ afterNewSixteen, TNFQuotientCompatible e.2 m := by
  intro m hm
  apply removeLastThree_sound 1500 (by decide)
  exact afterNewThirteen_sound m hm

noncomputable def globalNewSixteen := removeLastThree globalNewThirteen
theorem globalNewSixteen_count : globalNewSixteen.length = 213 := by decide +kernel
theorem globalNewSixteen_sound : ∀ m, compatible root m →
    WeightedBound 7014 m ∨ ∃ e ∈ globalNewSixteen, TNFQuotientCompatible e.2 m := by
  intro m hm
  exact removeLastThree_sound 7014 (by decide) m globalNewThirteen (globalNewThirteen_sound m hm)

theorem exact_at_target_newSixteen (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ globalNewSixteen, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB globalNewSixteen_sound hLeaves champ

#print axioms removeLastThree_sound
#print axioms new024_unique
#print axioms new034_unique
#print axioms new131_unique
#print axioms afterNewSixteen_count
#print axioms afterNewSixteen_sound
#print axioms globalNewSixteen_count
#print axioms globalNewSixteen_sound
#print axioms exact_at_target_newSixteen
end BB6.Agent47Raw41
