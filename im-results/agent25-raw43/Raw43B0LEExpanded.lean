import Raw43B0LEReduced
import Raw43B0LE_E0LAData
import Raw43B0LE_E0LFData
import Raw43B0LE_E1LEData
import Raw43B0LE_E1RAData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B0LE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
  BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
  BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent8TNFPath

def expandedResiduals := residuals.filter fun e =>
  !(equalTable e.2 BB6.Agent25Raw43B0LE_E0LA.p43child ||
    equalTable e.2 BB6.Agent25Raw43B0LE_E0LF.p43child ||
    equalTable e.2 BB6.Agent25Raw43B0LE_E1LE.p43child ||
    equalTable e.2 BB6.Agent25Raw43B0LE_E1RA.p43child)

theorem expandedResidual_count : expandedResiduals.length = 4 := by decide

theorem expandedReduced (m : Machine) (hm : TNFQuotientCompatible p m) :
    WeightedBound 2598 m ∨ ∃ e ∈ expandedResiduals, TNFQuotientCompatible e.2 m := by
  rcases reduced m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · by_cases h0 : equalTable e.2 BB6.Agent25Raw43B0LE_E0LA.p43child = true
    · rw [equalTable_sound h0] at hq
      have hb := quotientSafe BB6.Agent25Raw43B0LE_E0LA.p43child_root
        BB6.Agent25Raw43B0LE_E0LA.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h1 : equalTable e.2 BB6.Agent25Raw43B0LE_E0LF.p43child = true
    · rw [equalTable_sound h1] at hq
      have hb := quotientSafe BB6.Agent25Raw43B0LE_E0LF.p43child_root
        BB6.Agent25Raw43B0LE_E0LF.all43child m hq
      exact Or.inl hb
    by_cases h2 : equalTable e.2 BB6.Agent25Raw43B0LE_E1LE.p43child = true
    · rw [equalTable_sound h2] at hq
      have hb := quotientSafe BB6.Agent25Raw43B0LE_E1LE.p43child_root
        BB6.Agent25Raw43B0LE_E1LE.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h3 : equalTable e.2 BB6.Agent25Raw43B0LE_E1RA.p43child = true
    · rw [equalTable_sound h3] at hq
      have hb := quotientSafe BB6.Agent25Raw43B0LE_E1RA.p43child_root
        BB6.Agent25Raw43B0LE_E1RA.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    exact Or.inr ⟨e, by simp [expandedResiduals,he,h0,h1,h2,h3], hq⟩

theorem expandedCover {B : Nat} (hB : 2598 ≤ B)
    (hRest : ∀ e ∈ expandedResiduals, Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) p := by
  apply Cover.leaf
  intro m hm
  rcases expandedReduced m (compatible_quotient hm) with hb | ⟨e,he,hq⟩
  · intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) hB
  · have hr0 : e ∈ residuals := (List.mem_filter.mp he).1
    have hr : e ∈ remaining := (List.mem_filter.mp hr0).1
    have hf := of_decide_eq_true (List.all_eq_true.mp root_entries e hr)
    exact quotientSafe hf (hRest e he).sound m hq

#print axioms expandedResidual_count
#print axioms expandedReduced
#print axioms expandedCover
end BB6.Agent25Raw43B0LE
