import Raw109Refinement7
import Raw109B1LCData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent4Raw109Refinement8
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent4Raw109Cut BB6.Agent47CanonicalRefinement
open BB6.Agent47CanonicalFrontier

def remaining5 : List Move :=
  BB6.Agent4Raw109Refinement7.remaining6.filter fun mv =>
    decide (mv ≠ ⟨true,false,2⟩)

theorem remaining5_count : remaining5.length = 5 := by decide

theorem local_partition (m : Machine) (hm : compatible parent m) :
    WeightedBound 461 m ∨ ∃ mv ∈ remaining5, compatible (child mv) m := by
  rcases BB6.Agent4Raw109Refinement7.local_partition m hm with hb | ⟨mv,hr,hc⟩
  · exact Or.inl hb
  · by_cases hLC : mv = ⟨true,false,2⟩
    · subst mv
      exact Or.inl (fun k d hk hd => Nat.le_trans
        (BB6.Agent4Raw109B1LC.all_closed m hc k d hk hd) (by decide))
    · exact Or.inr ⟨mv,List.mem_filter.mpr ⟨hr,by simp [hLC]⟩,hc⟩

def replacement : List (List Move × PartialMachine) :=
  remaining5.map fun mv => ([mv], child mv)

noncomputable def roster82 :=
  graftRoster parent replacement BB6.Agent47Canonical78.roster

theorem roster_count : roster82.length = 82 := by decide

theorem roster_sound (m : Machine) (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 7014 m ∨ ∃ e ∈ roster82, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound (p := parent) (replacement := replacement)
    (by decide) BB6.Agent47Canonical78.roster_sound ?_ m hm
  intro t ht
  rcases local_partition t ht with hb | ⟨mv,hr,hc⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · exact Or.inr ⟨([mv],child mv),List.mem_map.mpr ⟨mv,hr,rfl⟩,hc⟩

theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ roster82, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) : BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB roster_sound hLeaves champ

#print axioms local_partition
#print axioms roster_count
#print axioms exact_at_target
end BB6.Agent4Raw109Refinement8
