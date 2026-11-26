import Raw140RootCut
import Raw140DeepCovers

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw140
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot

def matchesDeep (p : PartialMachine) : Bool :=
  BB6.Agent10Raw140Deep.closed.any (fun c => tableOK p c.table)
def afterDeep := before.filter (fun e => !matchesDeep e.2)

theorem afterDeep_count : afterDeep.length = 685 := by decide +kernel
theorem deep_root_entries : before.all (fun e => decide (e.2 initialSlot = some (some ⟨true,true,1⟩))) = true := by decide

theorem deep_sound (m : Machine) (hm : TNFQuotientCompatible parent m) :
    WeightedBound 10000 m ∨ ∃ e ∈ afterDeep, TNFQuotientCompatible e.2 m := by
  rcases root_sound m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases hs : matchesDeep e.2 = true
    · have hf := of_decide_eq_true (List.all_eq_true.mp deep_root_entries e he)
      have hc := BB6.Agent10Raw140Deep.matches_sound e.2 hs
      exact Or.inl (quotientSafe hf hc.sound m hq)
    · exact Or.inr ⟨e, by simp [afterDeep,he,hs], hq⟩

theorem cover_after_deep {B : Nat} (hB : 10000 ≤ B)
    (hRest : ∀ e ∈ afterDeep, Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) parent := by
  apply Cover.leaf
  intro m hm
  rcases deep_sound m (compatible_quotient hm) with hb | ⟨e,he,hq⟩
  · intro k d hk hd; exact Nat.le_trans (hb k d hk hd) hB
  · have he' : e ∈ before := (List.mem_filter.mp he).1
    have hf := of_decide_eq_true (List.all_eq_true.mp deep_root_entries e he')
    exact quotientSafe hf (hRest e he).sound m hq

#print axioms afterDeep_count
#print axioms cover_after_deep
end BB6.Agent10Raw140
