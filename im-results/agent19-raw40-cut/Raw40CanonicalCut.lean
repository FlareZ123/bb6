import CanonicalPartial
import Raw40Graft

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent31FourHoleRoster BB6.Agent50TNFPilot

theorem parent_support : TNFSupport parent 4 := supportOK_sound _ _ (by decide)

theorem canonical_checked : canonicalCheck 7014 parent 4 tree = true := by decide

def canonicalRemaining := canonicalResiduals parent 4 tree

theorem canonical_count : canonicalRemaining.length = 189 := by decide

theorem canonical_local_sound : ∀ m, TNFQuotientCompatible parent m → WeightedBound 7014 m ∨
    ∃ e ∈ canonicalRemaining, TNFQuotientCompatible e.2 m :=
  canonicalSound 7014 parent 4 tree (by decide) parent_support parent_root parent_nohalt canonical_checked

/-- Quotient-to-quotient graft: no composition of renamings is needed,
    because the local soundness theorem directly consumes the prior orbit. -/
theorem quotient_graft_sound {B : Nat} {r p : PartialMachine} {roster replacement : List (List Move × PartialMachine)}
    (hroot : ∀ m, compatible r m → WeightedBound B m ∨ ∃ e ∈ roster, TNFQuotientCompatible e.2 m)
    (hlocal : ∀ m, TNFQuotientCompatible p m → WeightedBound B m ∨ ∃ e ∈ replacement, TNFQuotientCompatible e.2 m) :
    ∀ m, compatible r m → WeightedBound B m ∨ ∃ e ∈ graftRoster p replacement roster, TNFQuotientCompatible e.2 m := by
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

noncomputable def canonicalRefinedRoster := graftRoster parent canonicalRemaining BB6.Agent47CanonicalRaw114Accepted.roster

theorem canonical_refined_count : canonicalRefinedRoster.length = 265 := by decide

theorem canonical_refined_sound : ∀ m, compatible root m → WeightedBound 7014 m ∨
    ∃ e ∈ canonicalRefinedRoster, TNFQuotientCompatible e.2 m :=
  quotient_graft_sound BB6.Agent47CanonicalRaw114Accepted.sound canonical_local_sound

theorem canonical_exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ canonicalRefinedRoster, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine, BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB canonical_refined_sound hLeaves champ

#print axioms canonical_local_sound
#print axioms quotient_graft_sound
#print axioms canonical_refined_sound
#print axioms canonical_exact_at_target
end BB6.Agent19Raw40
