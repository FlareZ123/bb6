import Raw41NewEightGraft
import Raw41New083Closed
import Raw41New084Closed
import Raw41New092Closed

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47Raw41
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31FourHoleRoster BB6.Agent50TNFPilot

/-- Original-source mixed FAR/AutoPump proofs discharge the last three
    distinct complete canonical Raw41 five-hole cylinders. -/
def removeMixedThree (xs : List (List Move × PartialMachine)) :=
  xs.filter fun e =>
    !(sameTable e.2 Raw41New083_p ||
      sameTable e.2 Raw41New084_p ||
      sameTable e.2 Raw41New092_p)

theorem removeMixedThree_sound (B : Nat) (hB : 737 ≤ B) (m : Machine)
    (xs : List (List Move × PartialMachine))
    (h : WeightedBound B m ∨ ∃ e ∈ xs, TNFQuotientCompatible e.2 m) :
    WeightedBound B m ∨ ∃ e ∈ removeMixedThree xs, TNFQuotientCompatible e.2 m := by
  rcases h with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases h83 : sameTable e.2 Raw41New083_p = true
    · exact Or.inl (fun k d hk hd =>
        Nat.le_trans (Raw41New083_bound m ((sameTable_sound h83) ▸ hq) k d hk hd) (by omega))
    · by_cases h84 : sameTable e.2 Raw41New084_p = true
      · exact Or.inl (fun k d hk hd =>
          Nat.le_trans (Raw41New084_bound m ((sameTable_sound h84) ▸ hq) k d hk hd) hB)
      · by_cases h92 : sameTable e.2 Raw41New092_p = true
        · exact Or.inl (fun k d hk hd =>
            Nat.le_trans (Raw41New092_bound m ((sameTable_sound h92) ▸ hq) k d hk hd) (by omega))
        · exact Or.inr ⟨e,List.mem_filter.mpr
            ⟨he, by simp [removeMixedThree, h83, h84, h92]⟩,hq⟩

def afterNewEleven := removeMixedThree afterNewEight

theorem new083_unique :
    (canonicalRemaining.filter fun e => sameTable e.2 Raw41New083_p).length = 1 := by decide +kernel
theorem new084_unique :
    (canonicalRemaining.filter fun e => sameTable e.2 Raw41New084_p).length = 1 := by decide +kernel
theorem new092_unique :
    (canonicalRemaining.filter fun e => sameTable e.2 Raw41New092_p).length = 1 := by decide +kernel
theorem afterNewEleven_count : afterNewEleven.length = 142 := by decide +kernel

theorem afterNewEleven_sound : ∀ m, TNFQuotientCompatible parent m →
    WeightedBound 1500 m ∨ ∃ e ∈ afterNewEleven, TNFQuotientCompatible e.2 m := by
  intro m hm
  apply removeMixedThree_sound 1500 (by decide)
  exact afterNewEight_sound m hm

noncomputable def globalNewEleven := removeMixedThree globalNewEight
theorem globalNewEleven_count : globalNewEleven.length = 218 := by decide +kernel
theorem globalNewEleven_sound : ∀ m, compatible root m →
    WeightedBound 7014 m ∨ ∃ e ∈ globalNewEleven, TNFQuotientCompatible e.2 m := by
  intro m hm
  exact removeMixedThree_sound 7014 (by decide) m globalNewEight (globalNewEight_sound m hm)

theorem exact_at_target_newEleven (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ globalNewEleven, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB globalNewEleven_sound hLeaves champ

#print axioms removeMixedThree_sound
#print axioms new083_unique
#print axioms new084_unique
#print axioms new092_unique
#print axioms afterNewEleven_count
#print axioms afterNewEleven_sound
#print axioms globalNewEleven_count
#print axioms globalNewEleven_sound
#print axioms exact_at_target_newEleven
end BB6.Agent47Raw41
