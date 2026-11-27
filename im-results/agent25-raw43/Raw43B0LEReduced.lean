import Raw43B0LECut
import Raw43B0LE_E0LCData
import Raw43B0LE_E0LEData
import Raw43B0LE_E0RAData
import Raw43B0LE_E0RBData
import Raw43B0LE_E0REData
import Raw43B0LE_E0RFData
import Raw43B0LE_E1LCData
import Raw43B0LE_E1RBData
import Raw43B0LE_E1REData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B0LE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent8TNFPath

def classified (q : PartialMachine) : Bool :=
  equalTable q BB6.Agent25Raw43B0LE_E0LC.p43child ||
  equalTable q BB6.Agent25Raw43B0LE_E0LE.p43child ||
  equalTable q BB6.Agent25Raw43B0LE_E0RA.p43child ||
  equalTable q BB6.Agent25Raw43B0LE_E0RB.p43child ||
  equalTable q BB6.Agent25Raw43B0LE_E0RE.p43child ||
  equalTable q BB6.Agent25Raw43B0LE_E0RF.p43child ||
  equalTable q BB6.Agent25Raw43B0LE_E1LC.p43child ||
  equalTable q BB6.Agent25Raw43B0LE_E1RB.p43child ||
  equalTable q BB6.Agent25Raw43B0LE_E1RE.p43child
def residuals := remaining.filter fun e => !classified e.2
theorem residual_count : residuals.length = 8 := by decide
theorem reduced (m : Machine) (hm : TNFQuotientCompatible p m) :
    WeightedBound 287 m ∨ ∃ e ∈ residuals, TNFQuotientCompatible e.2 m := by
  rcases sound m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases h0 : equalTable e.2 BB6.Agent25Raw43B0LE_E0LC.p43child = true
    · rw [equalTable_sound h0] at hq
      have hb := quotientSafe BB6.Agent25Raw43B0LE_E0LC.p43child_root BB6.Agent25Raw43B0LE_E0LC.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h1 : equalTable e.2 BB6.Agent25Raw43B0LE_E0LE.p43child = true
    · rw [equalTable_sound h1] at hq
      have hb := quotientSafe BB6.Agent25Raw43B0LE_E0LE.p43child_root BB6.Agent25Raw43B0LE_E0LE.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h2 : equalTable e.2 BB6.Agent25Raw43B0LE_E0RA.p43child = true
    · rw [equalTable_sound h2] at hq
      have hb := quotientSafe BB6.Agent25Raw43B0LE_E0RA.p43child_root BB6.Agent25Raw43B0LE_E0RA.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h3 : equalTable e.2 BB6.Agent25Raw43B0LE_E0RB.p43child = true
    · rw [equalTable_sound h3] at hq
      have hb := quotientSafe BB6.Agent25Raw43B0LE_E0RB.p43child_root BB6.Agent25Raw43B0LE_E0RB.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h4 : equalTable e.2 BB6.Agent25Raw43B0LE_E0RE.p43child = true
    · rw [equalTable_sound h4] at hq
      have hb := quotientSafe BB6.Agent25Raw43B0LE_E0RE.p43child_root BB6.Agent25Raw43B0LE_E0RE.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h5 : equalTable e.2 BB6.Agent25Raw43B0LE_E0RF.p43child = true
    · rw [equalTable_sound h5] at hq
      have hb := quotientSafe BB6.Agent25Raw43B0LE_E0RF.p43child_root BB6.Agent25Raw43B0LE_E0RF.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h6 : equalTable e.2 BB6.Agent25Raw43B0LE_E1LC.p43child = true
    · rw [equalTable_sound h6] at hq
      have hb := quotientSafe BB6.Agent25Raw43B0LE_E1LC.p43child_root BB6.Agent25Raw43B0LE_E1LC.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h7 : equalTable e.2 BB6.Agent25Raw43B0LE_E1RB.p43child = true
    · rw [equalTable_sound h7] at hq
      have hb := quotientSafe BB6.Agent25Raw43B0LE_E1RB.p43child_root BB6.Agent25Raw43B0LE_E1RB.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h8 : equalTable e.2 BB6.Agent25Raw43B0LE_E1RE.p43child = true
    · rw [equalTable_sound h8] at hq
      have hb := quotientSafe BB6.Agent25Raw43B0LE_E1RE.p43child_root BB6.Agent25Raw43B0LE_E1RE.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    exact Or.inr ⟨e, by simp [residuals,classified,he,h0,h1,h2,h3,h4,h5,h6,h7,h8], hq⟩

theorem cover {B : Nat} (hB : 287 ≤ B)
    (hRest : ∀ e ∈ residuals, Cover (WeightedBound B) e.2) : Cover (WeightedBound B) p := by
  apply Cover.leaf
  intro m hm
  rcases reduced m (compatible_quotient hm) with hb | ⟨e,he,hq⟩
  · intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) hB
  · have hr : e ∈ remaining := (List.mem_filter.mp he).1
    have hf := of_decide_eq_true (List.all_eq_true.mp root_entries e hr)
    exact quotientSafe hf (hRest e he).sound m hq

#print axioms residual_count
#print axioms reduced
#print axioms cover
end BB6.Agent25Raw43B0LE
