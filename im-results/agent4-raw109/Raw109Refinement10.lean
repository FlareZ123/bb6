import Raw109Refinement9
import Raw109B1LAData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent4Raw109Refinement10
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent4Raw109Cut BB6.Agent47CanonicalRefinement
open BB6.Agent47CanonicalFrontier

def remaining3 : List Move :=
  BB6.Agent4Raw109Refinement9.remaining4.filter fun mv =>
    decide (mv ≠ ⟨true,false,0⟩)

theorem remaining3_count : remaining3.length = 3 := by decide

theorem local_partition (m : Machine) (hm : compatible parent m) :
    WeightedBound 461 m ∨ ∃ mv ∈ remaining3, compatible (child mv) m := by
  rcases BB6.Agent4Raw109Refinement9.local_partition m hm with hb | ⟨mv,hr,hc⟩
  · exact Or.inl hb
  · by_cases hLA : mv = ⟨true,false,0⟩
    · subst mv
      exact Or.inl (fun k d hk hd => Nat.le_trans
        (BB6.Agent4Raw109B1LA.all_closed m hc k d hk hd) (by decide))
    · exact Or.inr ⟨mv,List.mem_filter.mpr ⟨hr,by simp [hLA]⟩,hc⟩

def replacement : List (List Move × PartialMachine) :=
  remaining3.map fun mv => ([mv], child mv)

noncomputable def roster80 :=
  graftRoster parent replacement BB6.Agent47Canonical78.roster

theorem roster_count : roster80.length = 80 := by decide

theorem roster_sound (m : Machine) (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 7014 m ∨ ∃ e ∈ roster80, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound (p := parent) (replacement := replacement)
    (by decide) BB6.Agent47Canonical78.roster_sound ?_ m hm
  intro t ht
  rcases local_partition t ht with hb | ⟨mv,hr,hc⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · exact Or.inr ⟨([mv],child mv),List.mem_map.mpr ⟨mv,hr,rfl⟩,hc⟩

theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ roster80, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) : BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB roster_sound hLeaves champ

#print axioms local_partition
#print axioms roster_count
#print axioms exact_at_target
end BB6.Agent4Raw109Refinement10
