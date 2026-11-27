import Raw41NewElevenGraft
import Raw41New116Closed
import Raw41New128Closed

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Raw41
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31FourHoleRoster BB6.Agent50TNFPilot

def removeNextTwo (xs : List (List Move × PartialMachine)) :=
  xs.filter fun e =>
    !(sameTable e.2 Raw41New116_p || sameTable e.2 Raw41New128_p)

theorem removeNextTwo_sound (B : Nat) (hB : 130 ≤ B) (m : Machine)
    (xs : List (List Move × PartialMachine))
    (h : WeightedBound B m ∨ ∃ e ∈ xs, TNFQuotientCompatible e.2 m) :
    WeightedBound B m ∨ ∃ e ∈ removeNextTwo xs, TNFQuotientCompatible e.2 m := by
  rcases h with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases h116 : sameTable e.2 Raw41New116_p = true
    · exact Or.inl (fun k d hk hd =>
        Nat.le_trans (Raw41New116_bound m ((sameTable_sound h116) ▸ hq) k d hk hd) (by omega))
    · by_cases h128 : sameTable e.2 Raw41New128_p = true
      · exact Or.inl (fun k d hk hd =>
          Nat.le_trans (Raw41New128_bound m ((sameTable_sound h128) ▸ hq) k d hk hd) hB)
      · exact Or.inr ⟨e,List.mem_filter.mpr
          ⟨he, by simp [removeNextTwo,h116,h128]⟩,hq⟩

def afterNewThirteen := removeNextTwo afterNewEleven

theorem new116_unique :
    (canonicalRemaining.filter fun e => sameTable e.2 Raw41New116_p).length = 1 := by decide +kernel
theorem new128_unique :
    (canonicalRemaining.filter fun e => sameTable e.2 Raw41New128_p).length = 1 := by decide +kernel
theorem afterNewThirteen_count : afterNewThirteen.length = 140 := by decide +kernel

theorem afterNewThirteen_sound : ∀ m, TNFQuotientCompatible parent m →
    WeightedBound 1500 m ∨ ∃ e ∈ afterNewThirteen, TNFQuotientCompatible e.2 m := by
  intro m hm
  apply removeNextTwo_sound 1500 (by decide)
  exact afterNewEleven_sound m hm

noncomputable def globalNewThirteen := removeNextTwo globalNewEleven
theorem globalNewThirteen_count : globalNewThirteen.length = 216 := by decide +kernel
theorem globalNewThirteen_sound : ∀ m, compatible root m →
    WeightedBound 7014 m ∨ ∃ e ∈ globalNewThirteen, TNFQuotientCompatible e.2 m := by
  intro m hm
  exact removeNextTwo_sound 7014 (by decide) m globalNewEleven (globalNewEleven_sound m hm)

theorem exact_at_target_newThirteen (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ globalNewThirteen, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB globalNewThirteen_sound hLeaves champ

#print axioms removeNextTwo_sound
#print axioms new116_unique
#print axioms new128_unique
#print axioms afterNewThirteen_count
#print axioms afterNewThirteen_sound
#print axioms globalNewThirteen_count
#print axioms globalNewThirteen_sound
#print axioms exact_at_target_newThirteen
end BB6.Agent47Raw41
