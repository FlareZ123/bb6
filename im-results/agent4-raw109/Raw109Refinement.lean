import Raw109Cut
import Raw109B1REData
import Raw109B0LCData
import Canonical78Roster
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent4Raw109Refinement
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent4Raw109Cut BB6.Agent47CanonicalRefinement
open BB6.Agent47CanonicalFrontier

def remaining9 : List Move :=
  remaining.filter fun mv => decide (mv ≠ ⟨true,true,4⟩ ∧ mv ≠ ⟨false,false,2⟩)

theorem remaining9_count : remaining9.length = 9 := by decide

theorem local_partition (m : Machine) (hm : compatible parent m) :
    WeightedBound 353 m ∨ ∃ mv ∈ remaining9, compatible (child mv) m := by
  rcases parent_dichotomy m hm with hb | ⟨mv,hr,hc⟩
  · exact Or.inl hb
  · by_cases hRE : mv = ⟨true,true,4⟩
    · subst mv
      left
      intro k d hk hd
      exact Nat.le_trans (BB6.Agent4Raw109B1RE.all_closed m hc k d hk hd) (by decide)
    · by_cases hLC : mv = ⟨false,false,2⟩
      · subst mv
        left
        intro k d hk hd
        exact Nat.le_trans (BB6.Agent4Raw109B0LC.all_closed m hc k d hk hd) (by decide)
      · exact Or.inr ⟨mv,List.mem_filter.mpr ⟨hr,by simp [hRE,hLC]⟩,hc⟩

def replacement : List (List Move × PartialMachine) :=
  remaining9.map fun mv => ([mv], child mv)

noncomputable def roster86 :=
  graftRoster parent replacement BB6.Agent47Canonical78.roster

theorem roster_count : roster86.length = 86 := by decide

theorem roster_sound (m : Machine) (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 7014 m ∨ ∃ e ∈ roster86, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound (p := parent) (replacement := replacement)
    (by decide) BB6.Agent47Canonical78.roster_sound ?_ m hm
  intro t ht
  rcases local_partition t ht with hb | ⟨mv,hr,hc⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · exact Or.inr ⟨([mv],child mv),List.mem_map.mpr ⟨mv,hr,rfl⟩,hc⟩

theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ roster86, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB roster_sound hLeaves champ

#print axioms remaining9_count
#print axioms local_partition
#print axioms roster_count
#print axioms roster_sound
#print axioms exact_at_target
end BB6.Agent4Raw109Refinement
