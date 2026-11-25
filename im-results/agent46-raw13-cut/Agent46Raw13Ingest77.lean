import Agent46Raw13Data
import CanonicalRaw114Accepted

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent46Raw13Canonical77
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent46CanonicalCut
open BB6.Agent31FourHoleRoster BB6.Agent47CanonicalFrontier
open BB6.Agent46Raw13

abbrev Entry := List Move × PartialMachine

/-- The raw13 parent survives the independently source-accepted raw114 cut
    exactly once in the current 77-entry canonical roster. -/
theorem parent_count77 :
    (BB6.Agent47CanonicalRaw114Accepted.roster.filter
      fun e => sameTable e.2 raw13).length = 1 := by
  decide

def graftEntry77 (e : Entry) : List Entry :=
  if sameTable e.2 raw13 then
    raw13Residuals.map fun r => (e.1 ++ r.1, r.2)
  else [e]

noncomputable def graft77 (roster : List Entry) : List Entry :=
  roster.flatMap graftEntry77

noncomputable def refinedRoster77 :=
  graft77 BB6.Agent47CanonicalRaw114Accepted.roster

/-- Replace the raw13 representative inside any source-rooted quotient
    roster. The local raw13 proof is used only at the matching parent;
    every other quotient representative is retained unchanged. -/
theorem graft_sound77 {roster : List Entry} {C : Nat}
    (hC : C ≤ 21269)
    (hroot : ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound C m ∨ ∃ e ∈ roster, TNFQuotientCompatible e.2 m)
    (m : Machine) (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 21269 m ∨
      ∃ e ∈ graft77 roster, TNFQuotientCompatible e.2 m := by
  rcases hroot m hm with hb | ⟨e, he, hq⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) hC)
  · by_cases hmatch : sameTable e.2 raw13 = true
    · have heq := sameTable_sound hmatch
      have hc : TNFQuotientCompatible raw13 m := heq ▸ hq
      rcases BB6.Agent46Raw13.raw13_sound m hc with hb | ⟨r, hr, hrc⟩
      · exact Or.inl hb
      · refine Or.inr ⟨(e.1 ++ r.1, r.2),
          List.mem_flatMap.mpr ⟨e, he, ?_⟩, hrc⟩
        simp only [graftEntry77, hmatch, ite_true]
        exact List.mem_map.mpr ⟨r, hr, rfl⟩
    · exact Or.inr ⟨e, List.mem_flatMap.mpr
        ⟨e, he, by simp [graftEntry77, hmatch]⟩, hq⟩

/-- The 77-roster graft retains 76 unchanged representatives and replaces
    raw13 by exactly the residual list certified by the current raw13 cut. -/
theorem refined_count77 :
    refinedRoster77.length = 76 + raw13Residuals.length := by
  decide

theorem refined_sound77 (m : Machine)
    (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 21269 m ∨
      ∃ e ∈ refinedRoster77, TNFQuotientCompatible e.2 m :=
  graft_sound77 (by decide)
    BB6.Agent47CanonicalRaw114Accepted.sound m hm

theorem cover_at_target77 (B : Nat) (hB : 21269 ≤ B)
    (hLeaves : ∀ e ∈ refinedRoster77, Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) BB6.CoverageAdapter.firstOneCylinder :=
  cover_of_quotient_roster hB refined_sound77 hLeaves

/-- Conditional exactness after both raw114 and raw13 are ingested.
    No claim is made until every one of the 1792 retained Covers is proved. -/
theorem exact_at_target77 (B : Nat) (hB : 21269 ≤ B)
    (hLeaves : ∀ e ∈ refinedRoster77, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB refined_sound77 hLeaves champ

#print axioms parent_count77
#print axioms refined_count77
#print axioms refined_sound77
#print axioms cover_at_target77
#print axioms exact_at_target77

end BB6.Agent46Raw13Canonical77
