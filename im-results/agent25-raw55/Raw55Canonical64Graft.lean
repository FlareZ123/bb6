import Raw55Cut
import Canonical64Raw120Integrated
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent25Raw55Canonical64Graft
open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier
open BB6.Agent47CanonicalRefinement
open BB6.Agent50TNFPilot

abbrev raw55Parent : PartialMachine := BB6.Agent25Raw55Cut.parent
abbrev raw55Replacement := BB6.Agent25Raw55Cut.canonicalRemaining

/-- Exact membership gate against the current source-accepted 64-way frontier. -/
theorem raw55_parent_count :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 raw55Parent)).length = 1 := by decide

/-- Replace exactly the Raw55 parent by its complete explicit quotient complement. -/
noncomputable def canonical64RefinedRoster :=
  graftRoster raw55Parent raw55Replacement BB6.Agent3Canonical64Raw120.roster64

theorem canonical64Refined_count : canonical64RefinedRoster.length = 337 := by decide

/-- Quotient-to-quotient graft: the local proof consumes the prior quotient
    orbit directly, so no state-permutation composition is required. -/
theorem quotient_graft_sound {B : Nat} {r p : PartialMachine}
    {roster replacement : List (List Move × PartialMachine)}
    (hroot : ∀ m, compatible r m →
      WeightedBound B m ∨ ∃ e ∈ roster, TNFQuotientCompatible e.2 m)
    (hlocal : ∀ m, TNFQuotientCompatible p m →
      WeightedBound B m ∨ ∃ e ∈ replacement, TNFQuotientCompatible e.2 m) :
    ∀ m, compatible r m →
      WeightedBound B m ∨ ∃ e ∈ graftRoster p replacement roster,
        TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases hroot m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases ht : sameTable e.2 p = true
    · have eq : e.2 = p := sameTable_sound ht
      rcases hlocal m (eq ▸ hq) with hb | ⟨e',he',hq'⟩
      · exact Or.inl hb
      · refine Or.inr ⟨(e.1 ++ e'.1,e'.2),?_,hq'⟩
        apply List.mem_flatMap.mpr
        exact ⟨e,he,by simp only [graftEntry,ht,if_true]; exact List.mem_map.mpr ⟨e',he',rfl⟩⟩
    · exact Or.inr ⟨e,List.mem_flatMap.mpr ⟨e,he,by simp [graftEntry,ht]⟩,hq⟩

/-- Lift Raw55's local 7014 certificate to the common Canonical64 floor. -/
theorem raw55_local_sound_6766859 :
    ∀ m, TNFQuotientCompatible raw55Parent m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ raw55Replacement, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases BB6.Agent25Raw55Cut.canonical_local_sound m hm with hb | hres
  · exact Or.inl (by
      intro k d hk hd
      exact Nat.le_trans (hb k d hk hd) (by decide))
  · exact Or.inr hres

/-- Current global conditional frontier with Raw55 replaced by 274 explicit
    residuals. This is a refinement, not a net reduction in representative
    count and not a complete BB(6) upper bound. -/
theorem canonical64Refined_sound :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ canonical64RefinedRoster, TNFQuotientCompatible e.2 m :=
  quotient_graft_sound BB6.Agent3Canonical64Raw120.sound64_integrated
    raw55_local_sound_6766859

#print axioms raw55_parent_count
#print axioms canonical64Refined_count
#print axioms raw55_local_sound_6766859
#print axioms canonical64Refined_sound
end BB6.Agent25Raw55Canonical64Graft
