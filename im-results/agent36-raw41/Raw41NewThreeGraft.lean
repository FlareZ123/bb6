import Raw41CanonicalCut
import Raw41New088Closed
import Raw41New090Closed
import Raw41New123Closed

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Raw41
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31FourHoleRoster BB6.Agent50TNFPilot

/-- Exact complement of three distinct source-checked 5-hole cylinders. -/
def removeNewThree (xs : List (List Move × PartialMachine)) :=
  xs.filter fun e =>
    !(sameTable e.2 Raw41New088_p ||
      sameTable e.2 Raw41New090_p ||
      sameTable e.2 Raw41New123_p)

/-- Discharge exactly the original three finite-automaton complete cylinders. -/
theorem removeNewThree_sound (B : Nat) (hB : 84 ≤ B) (m : Machine)
    (xs : List (List Move × PartialMachine))
    (h : WeightedBound B m ∨ ∃ e ∈ xs, TNFQuotientCompatible e.2 m) :
    WeightedBound B m ∨ ∃ e ∈ removeNewThree xs, TNFQuotientCompatible e.2 m := by
  rcases h with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases h88 : sameTable e.2 Raw41New088_p = true
    · exact Or.inl (fun k d hk hd =>
        Nat.le_trans (Raw41New088_bound m ((sameTable_sound h88) ▸ hq) k d hk hd) (by omega))
    · by_cases h90 : sameTable e.2 Raw41New090_p = true
      · exact Or.inl (fun k d hk hd =>
          Nat.le_trans (Raw41New090_bound m ((sameTable_sound h90) ▸ hq) k d hk hd) hB)
      · by_cases h123 : sameTable e.2 Raw41New123_p = true
        · exact Or.inl (fun k d hk hd =>
            Nat.le_trans (Raw41New123_bound m ((sameTable_sound h123) ▸ hq) k d hk hd) (by omega))
        · exact Or.inr ⟨e,List.mem_filter.mpr
            ⟨he, by simp [removeNewThree, h88, h90, h123]⟩,hq⟩

def afterNewThree := removeNewThree canonicalRemaining

theorem new088_unique :
    (canonicalRemaining.filter fun e => sameTable e.2 Raw41New088_p).length = 1 := by decide +kernel
theorem new090_unique :
    (canonicalRemaining.filter fun e => sameTable e.2 Raw41New090_p).length = 1 := by decide +kernel
theorem new123_unique :
    (canonicalRemaining.filter fun e => sameTable e.2 Raw41New123_p).length = 1 := by decide +kernel
theorem afterNewThree_count : afterNewThree.length = 150 := by decide +kernel

theorem afterNewThree_sound : ∀ m, TNFQuotientCompatible parent m →
    WeightedBound 84 m ∨ ∃ e ∈ afterNewThree, TNFQuotientCompatible e.2 m := by
  intro m hm
  apply removeNewThree_sound 84 (by decide)
  rcases canonical_sound m hm with hb | h
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · exact Or.inr h

noncomputable def globalNewThree := removeNewThree roster
theorem globalNewThree_count : globalNewThree.length = 226 := by decide +kernel

theorem globalNewThree_sound : ∀ m, compatible root m →
    WeightedBound 7014 m ∨ ∃ e ∈ globalNewThree, TNFQuotientCompatible e.2 m := by
  intro m hm
  exact removeNewThree_sound 7014 (by decide) m roster (roster_sound m hm)

theorem exact_at_target_newThree (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ globalNewThree, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB globalNewThree_sound hLeaves champ

#print axioms removeNewThree_sound
#print axioms new088_unique
#print axioms new090_unique
#print axioms new123_unique
#print axioms afterNewThree_count
#print axioms afterNewThree_sound
#print axioms globalNewThree_count
#print axioms globalNewThree_sound
#print axioms exact_at_target_newThree
end BB6.Agent47Raw41
