import Agent46Raw13Data
import Canonical78Roster

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent46Raw13
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent46CanonicalCut
open BB6.Agent31FourHoleRoster
abbrev Entry := List Move × PartialMachine

/-- The actual canonical78 parent occurs exactly once. Equality is tested
    over all twelve transition slots, not over a diagnostic index. -/
theorem parent_count :
    (BB6.Agent47Canonical78.roster.filter fun e => sameTable e.2 raw13).length = 1 := by
  decide

def graftEntry (e : Entry) : List Entry :=
  if sameTable e.2 raw13 then raw13Residuals.map fun r => (e.1 ++ r.1,r.2) else [e]

noncomputable def graft (roster : List Entry) : List Entry :=
  roster.flatMap graftEntry

noncomputable def refinedRoster := graft BB6.Agent47Canonical78.roster

/-- The quotient-aware cut composes with any source-rooted quotient roster.
    Unlike a raw-table cut, the residual obligation remains quotient
    compatible after each least-fresh-label choice. -/
theorem graft_sound {roster : List Entry}
    (hroot : ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 7014 m ∨ ∃ e ∈ roster, TNFQuotientCompatible e.2 m)
    (m : Machine) (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 7014 m ∨ ∃ e ∈ graft roster, TNFQuotientCompatible e.2 m := by
  rcases hroot m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases hmatch : sameTable e.2 raw13 = true
    · have heq := sameTable_sound hmatch
      have hc : TNFQuotientCompatible raw13 m := heq ▸ hq
      rcases raw13_sound m hc with hb | ⟨r,hr,hrc⟩
      · exact Or.inl hb
      · refine Or.inr ⟨(e.1 ++ r.1,r.2), List.mem_flatMap.mpr ⟨e,he,?_⟩,hrc⟩
        simp only [graftEntry,hmatch,ite_true]
        exact List.mem_map.mpr ⟨r,hr,rfl⟩
    · exact Or.inr ⟨e,List.mem_flatMap.mpr ⟨e,he,by simp [graftEntry,hmatch]⟩,hq⟩

theorem refined_count : refinedRoster.length = 1799 := by decide

theorem refined_sound (m : Machine) (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 7014 m ∨ ∃ e ∈ refinedRoster, TNFQuotientCompatible e.2 m :=
  graft_sound BB6.Agent47Canonical78.roster_sound m hm

theorem cover_at_target (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ refinedRoster, Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) BB6.CoverageAdapter.firstOneCylinder :=
  BB6.Agent47CanonicalFrontier.cover_of_quotient_roster hB refined_sound hLeaves

/-- The authentic #754 one-hole cylinder. It is retained by this cut:
    no finite timeout has been converted into a proof of nonhalting. -/
def oneHole754 : PartialMachine :=
  refine (refine (refine (refine (refine (refine (refine (refine
    raw13 (0,true) (some ⟨true,false,2⟩))
    (2,true) (some ⟨false,true,1⟩))
    (1,true) (some ⟨false,false,3⟩))
    (3,false) (some ⟨true,false,1⟩))
    (3,true) (some ⟨true,false,4⟩))
    (4,false) (some ⟨true,true,5⟩))
    (5,true) (some ⟨false,true,4⟩))
    (4,true) (some ⟨false,false,0⟩)

theorem oneHole754_retained :
    ∃ e ∈ raw13Residuals, e.2 = oneHole754 := by
  have hh : raw13Residuals.any (fun e => sameTable e.2 oneHole754) = true := by decide
  obtain ⟨e,he,h⟩ := List.any_eq_true.mp hh
  exact ⟨e,he,sameTable_sound h⟩

#print axioms parent_count
#print axioms refined_count
#print axioms refined_sound
#print axioms cover_at_target
#print axioms oneHole754_retained

end BB6.Agent46Raw13
