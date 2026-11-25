import Raw110Cut
import Canonical78Roster
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw110
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47Canonical78 BB6.Agent47CanonicalFrontier
open BB6.Agent31ThreeHole

theorem p110_mem : ∃ e ∈ roster, e.2 = p110 := by
  have h : roster.any (fun e => tableOK e.2 p110) = true := by decide
  obtain ⟨e,he,hcheck⟩ := List.any_eq_true.mp h
  exact ⟨e,he,tableOK_sound _ _ hcheck⟩

/-- Replace exactly one canonical cylinder by its nine retained descendants.
    The inherited quotient permutation is unchanged on the refined table. -/
noncomputable def refinedRoster : List (List Move × PartialMachine) :=
  roster.flatMap fun e =>
    if tableOK e.2 p110 then
      residual110.map fun r => (e.1 ++ r.1,r.2)
    else [e]

theorem refined_count : refinedRoster.length = 86 := by decide

theorem refined_sound (m : Machine)
    (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 7014 m ∨ ∃ e ∈ refinedRoster, TNFQuotientCompatible e.2 m := by
  rcases roster_sound m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases hc : tableOK e.2 p110 = true
    · rcases hq with ⟨perm,hperm,hcomp⟩
      have heq := tableOK_sound e.2 p110 hc
      rw [heq] at hcomp
      rcases raw110_sound _ hcomp with hb | ⟨r,hr,hcompat⟩
      · have hz := firstOne_terminal BB6.Agent50TNFPilot.root rfl m hm
        exact Or.inl (weighted_rename_back 7014 perm m hperm hz hb)
      · exact Or.inr ⟨(e.1 ++ r.1,r.2),
          List.mem_flatMap.mpr ⟨e,he,by simp only [hc,if_true]; exact List.mem_map.mpr ⟨r,hr,rfl⟩⟩,
          ⟨perm,hperm,hcompat⟩⟩
    · exact Or.inr ⟨e,List.mem_flatMap.mpr ⟨e,he,by simp [hc]⟩,hq⟩

theorem exact_at_target_refined (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ refinedRoster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB refined_sound hLeaves champ

#print axioms p110_mem
#print axioms refined_count
#print axioms refined_sound
#print axioms exact_at_target_refined
end BB6.Agent7Raw110
