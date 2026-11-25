import Raw109Refinement
import Raw109B1LBData
import Raw109B0RFData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent4Raw109Refinement6
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent4Raw109Cut BB6.Agent47CanonicalRefinement
open BB6.Agent47CanonicalFrontier

def remaining7 : List Move :=
  BB6.Agent4Raw109Refinement.remaining9.filter fun mv =>
    decide (mv ≠ ⟨true,false,1⟩ ∧ mv ≠ ⟨false,true,5⟩)

theorem remaining7_count : remaining7.length = 7 := by decide

theorem local_partition (m : Machine) (hm : compatible parent m) :
    WeightedBound 461 m ∨ ∃ mv ∈ remaining7, compatible (child mv) m := by
  rcases BB6.Agent4Raw109Refinement.local_partition m hm with hb | ⟨mv,hr,hc⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · by_cases hLB : mv = ⟨true,false,1⟩
    · subst mv
      exact Or.inl (fun k d hk hd => Nat.le_trans
        (BB6.Agent4Raw109B1LB.all_closed m hc k d hk hd) (by decide))
    · by_cases hRF : mv = ⟨false,true,5⟩
      · subst mv
        exact Or.inl (BB6.Agent4Raw109B0RF.all_closed m hc)
      · exact Or.inr ⟨mv,List.mem_filter.mpr ⟨hr,by simp [hLB,hRF]⟩,hc⟩

def replacement : List (List Move × PartialMachine) :=
  remaining7.map fun mv => ([mv], child mv)

noncomputable def roster84 :=
  graftRoster parent replacement BB6.Agent47Canonical78.roster

theorem roster_count : roster84.length = 84 := by decide

theorem roster_sound (m : Machine) (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 7014 m ∨ ∃ e ∈ roster84, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound (p := parent) (replacement := replacement)
    (by decide) BB6.Agent47Canonical78.roster_sound ?_ m hm
  intro t ht
  rcases local_partition t ht with hb | ⟨mv,hr,hc⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · exact Or.inr ⟨([mv],child mv),List.mem_map.mpr ⟨mv,hr,rfl⟩,hc⟩

theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ roster84, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) : BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB roster_sound hLeaves champ

#print axioms local_partition
#print axioms roster_count
#print axioms exact_at_target
end BB6.Agent4Raw109Refinement6
