import Raw43ParentCutExpandedFive
import Raw43B0LACompose
import Raw43B1LACompose
import Raw43B1LECompose
import Raw43B1RECompose
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43ParentExpandedNine
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
  BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
  BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent8TNFPath
  BB6.Agent25Raw43Parent

def remaining := BB6.Agent25Raw43ParentExpandedFive.remaining.filter fun e =>
  !(equalTable e.2 BB6.Agent25Raw43B0LA.p ||
    equalTable e.2 BB6.Agent25Raw43B1LA.p ||
    equalTable e.2 BB6.Agent25Raw43B1LE.p ||
    equalTable e.2 BB6.Agent25Raw43B1RE.p)

theorem remaining_count : remaining.length = 1 := by decide
theorem root_entries : remaining.all (fun e =>
    decide (e.2 initialSlot = some (some ⟨true,true,1⟩))) = true := by decide

theorem sound (m : Machine) (hm : TNFQuotientCompatible parent m) :
    WeightedBound 11292 m ∨ ∃ e ∈ remaining, TNFQuotientCompatible e.2 m := by
  rcases BB6.Agent25Raw43ParentExpandedFive.sound m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · by_cases h0 : equalTable e.2 BB6.Agent25Raw43B0LA.p = true
    · rw [equalTable_sound h0] at hq
      have hb := BB6.Agent25Raw43B0LA.all_quotient m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h1 : equalTable e.2 BB6.Agent25Raw43B1LA.p = true
    · rw [equalTable_sound h1] at hq
      have hb := BB6.Agent25Raw43B1LA.all_quotient_full m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h2 : equalTable e.2 BB6.Agent25Raw43B1LE.p = true
    · rw [equalTable_sound h2] at hq
      have hb := BB6.Agent25Raw43B1LE.all_quotient m hq
      exact Or.inl hb
    by_cases h3 : equalTable e.2 BB6.Agent25Raw43B1RE.p = true
    · rw [equalTable_sound h3] at hq
      have hb := BB6.Agent25Raw43B1RE.all_quotient m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    exact Or.inr ⟨e, by simp [remaining,he,h0,h1,h2,h3], hq⟩

theorem cover {B : Nat} (hB : 11292 ≤ B)
    (hRest : ∀ e ∈ remaining, Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) parent := by
  apply Cover.leaf
  intro m hm
  rcases sound m (compatible_quotient hm) with hb | ⟨e,he,hq⟩
  · intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) hB
  · have hf := of_decide_eq_true (List.all_eq_true.mp root_entries e he)
    exact quotientSafe hf (hRest e he).sound m hq

#print axioms remaining_count
#print axioms sound
#print axioms cover
end BB6.Agent25Raw43ParentExpandedNine
