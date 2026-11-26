import Raw140RootCut
import Nov26Pair1
import Nov26Pair2
import Nov26Pair3
import Nov26Pair10

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw140
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot
open BB6.Agent10Nov26

def sourceLeaves : List PartialMachine :=
  [leaf n4, leaf n5, leaf n8, leaf n12, leaf n16, leaf n19, leaf n20]

private theorem never_weighted {p : PartialMachine} {B : Nat}
    (h : Cover NeverHalts p) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (h.sound m hm))

theorem source_safe {p : PartialMachine} {B : Nat}
    (hp : p ∈ sourceLeaves) : Cover (WeightedBound B) p := by
  simp only [sourceLeaves, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h|h|h|h|h|h|h <;> subst p
  · exact never_weighted n4_cover
  · exact never_weighted n5_cover
  · exact never_weighted n8_cover
  · exact never_weighted n12_cover
  · exact never_weighted n16_cover
  · exact never_weighted n19_cover
  · exact never_weighted n20_cover

def matchesSource (p : PartialMachine) : Bool := sourceLeaves.any (fun q => sameTable p q)
def remaining := before.filter (fun e => !matchesSource e.2)
theorem all_sources_present : sourceLeaves.all (fun p => before.any (fun e => sameTable p e.2)) = true := by decide
theorem remaining_count : remaining.length = 807 := by decide
theorem root_entries : before.all (fun e => decide (e.2 initialSlot = some (some ⟨true,true,1⟩))) = true := by decide

theorem sound (m : Machine) (hm : TNFQuotientCompatible parent m) :
    WeightedBound 10000 m ∨ ∃ e ∈ remaining, TNFQuotientCompatible e.2 m := by
  rcases root_sound m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases hs : matchesSource e.2 = true
    · obtain ⟨p,hp,ht⟩ := List.any_eq_true.mp hs
      have heq := sameTable_sound ht
      have hf := of_decide_eq_true (List.all_eq_true.mp root_entries e he)
      have hc : Cover (WeightedBound 10000) p := source_safe hp
      rw [← heq] at hc
      exact Or.inl (quotientSafe hf hc.sound m hq)
    · exact Or.inr ⟨e, by simp [remaining,he,hs], hq⟩

theorem cover_at_bound {B : Nat} (hB : 10000 ≤ B)
    (hRest : ∀ e ∈ remaining, Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) parent := by
  apply Cover.leaf
  intro m hm
  rcases sound m (compatible_quotient hm) with hb | ⟨e,he,hq⟩
  · intro k d hk hd; exact Nat.le_trans (hb k d hk hd) hB
  · have he' : e ∈ before := (List.mem_filter.mp he).1
    have hf := of_decide_eq_true (List.all_eq_true.mp root_entries e he')
    exact quotientSafe hf (hRest e he).sound m hq

#print axioms all_sources_present
#print axioms remaining_count
#print axioms sound
#print axioms cover_at_bound
end BB6.Agent10Raw140
