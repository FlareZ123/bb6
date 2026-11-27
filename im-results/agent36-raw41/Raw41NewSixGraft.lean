import Raw41NewThreeGraft
import Raw41New099Closed
import Raw41New101Closed
import Raw41New134Closed

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Raw41
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31FourHoleRoster BB6.Agent50TNFPilot

def removeLaterThree (xs : List (List Move × PartialMachine)) :=
  xs.filter fun e =>
    !(sameTable e.2 Raw41New099_p ||
      sameTable e.2 Raw41New101_p ||
      sameTable e.2 Raw41New134_p)

theorem removeLaterThree_sound (B : Nat) (hB : 167 ≤ B) (m : Machine)
    (xs : List (List Move × PartialMachine))
    (h : WeightedBound B m ∨ ∃ e ∈ xs, TNFQuotientCompatible e.2 m) :
    WeightedBound B m ∨ ∃ e ∈ removeLaterThree xs, TNFQuotientCompatible e.2 m := by
  rcases h with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases h99 : sameTable e.2 Raw41New099_p = true
    · exact Or.inl (fun k d hk hd =>
        Nat.le_trans (Raw41New099_bound m ((sameTable_sound h99) ▸ hq) k d hk hd) (by omega))
    · by_cases h101 : sameTable e.2 Raw41New101_p = true
      · exact Or.inl (fun k d hk hd =>
          Nat.le_trans (Raw41New101_bound m ((sameTable_sound h101) ▸ hq) k d hk hd) (by omega))
      · by_cases h134 : sameTable e.2 Raw41New134_p = true
        · exact Or.inl (fun k d hk hd =>
            Nat.le_trans (Raw41New134_bound m ((sameTable_sound h134) ▸ hq) k d hk hd) hB)
        · exact Or.inr ⟨e,List.mem_filter.mpr
            ⟨he, by simp [removeLaterThree, h99, h101, h134]⟩,hq⟩

def afterNewSix := removeLaterThree afterNewThree
theorem new099_unique :
    (canonicalRemaining.filter fun e => sameTable e.2 Raw41New099_p).length = 1 := by decide +kernel
theorem new101_unique :
    (canonicalRemaining.filter fun e => sameTable e.2 Raw41New101_p).length = 1 := by decide +kernel
theorem new134_unique :
    (canonicalRemaining.filter fun e => sameTable e.2 Raw41New134_p).length = 1 := by decide +kernel
theorem afterNewSix_count : afterNewSix.length = 147 := by decide +kernel
theorem afterNewSix_sound : ∀ m, TNFQuotientCompatible parent m →
    WeightedBound 167 m ∨ ∃ e ∈ afterNewSix, TNFQuotientCompatible e.2 m := by
  intro m hm
  apply removeLaterThree_sound 167 (by decide)
  rcases afterNewThree_sound m hm with hb | h
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · exact Or.inr h

noncomputable def globalNewSix := removeLaterThree globalNewThree
theorem globalNewSix_count : globalNewSix.length = 223 := by decide +kernel
theorem globalNewSix_sound : ∀ m, compatible root m →
    WeightedBound 7014 m ∨ ∃ e ∈ globalNewSix, TNFQuotientCompatible e.2 m := by
  intro m hm
  exact removeLaterThree_sound 7014 (by decide) m globalNewThree (globalNewThree_sound m hm)

theorem exact_at_target_newSix (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ globalNewSix, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB globalNewSix_sound hLeaves champ

#print axioms removeLaterThree_sound
#print axioms new099_unique
#print axioms new101_unique
#print axioms new134_unique
#print axioms afterNewSix_count
#print axioms afterNewSix_sound
#print axioms globalNewSix_count
#print axioms globalNewSix_sound
#print axioms exact_at_target_newSix
end BB6.Agent47Raw41
