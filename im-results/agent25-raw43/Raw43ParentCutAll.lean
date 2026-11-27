import Raw43ParentCut
import Raw43RD1Data
import Raw43E0REData
import Raw43E1REData
import Raw43E0RFData
import Raw43E1LBData
import Raw43E0RCData
import Raw43E0LFData
import Raw43E1LAData
import Raw43E1LEData
import Raw43E1RFData
import Raw43E1LFData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43ParentAll
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent8TNFPath BB6.Agent25Raw43Parent
def remaining := before.filter fun e =>
  !(equalTable e.2 BB6.Agent25Raw43.p43child ||
    equalTable e.2 BB6.Agent25Raw43RD.p43child ||
    equalTable e.2 BB6.Agent25Raw43RD1.p43child ||
    equalTable e.2 BB6.Agent25Raw43E0RE.p43child ||
    equalTable e.2 BB6.Agent25Raw43E1RE.p43child ||
    equalTable e.2 BB6.Agent25Raw43E0RF.p43child ||
    equalTable e.2 BB6.Agent25Raw43E1LB.p43child ||
    equalTable e.2 BB6.Agent25Raw43E0RC.p43child ||
    equalTable e.2 BB6.Agent25Raw43E0LF.p43child ||
    equalTable e.2 BB6.Agent25Raw43E1LA.p43child ||
    equalTable e.2 BB6.Agent25Raw43E1LE.p43child ||
    equalTable e.2 BB6.Agent25Raw43E1RF.p43child ||
    equalTable e.2 BB6.Agent25Raw43E1LF.p43child)
theorem remaining_count : remaining.length = 10 := by decide
theorem root_entries : remaining.all (fun e => decide (e.2 initialSlot = some (some ⟨true,true,1⟩))) = true := by decide
theorem sound (m : Machine) (hm : TNFQuotientCompatible parent m) :
    WeightedBound 1713 m ∨ ∃ e ∈ remaining, TNFQuotientCompatible e.2 m := by
  rcases canonicalSound 75 parent 4 tree (by decide) parent_support parent_root parent_nohalt checked m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · by_cases h0 : equalTable e.2 BB6.Agent25Raw43.p43child = true
    · rw [equalTable_sound h0] at hq
      have hb := quotientSafe BB6.Agent25Raw43.p43child_root BB6.Agent25Raw43.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h1 : equalTable e.2 BB6.Agent25Raw43RD.p43child = true
    · rw [equalTable_sound h1] at hq
      have hb := quotientSafe BB6.Agent25Raw43RD.p43child_root BB6.Agent25Raw43RD.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h2 : equalTable e.2 BB6.Agent25Raw43RD1.p43child = true
    · rw [equalTable_sound h2] at hq
      have hb := quotientSafe BB6.Agent25Raw43RD1.p43child_root BB6.Agent25Raw43RD1.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h3 : equalTable e.2 BB6.Agent25Raw43E0RE.p43child = true
    · rw [equalTable_sound h3] at hq
      have hb := quotientSafe BB6.Agent25Raw43E0RE.p43child_root BB6.Agent25Raw43E0RE.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h4 : equalTable e.2 BB6.Agent25Raw43E1RE.p43child = true
    · rw [equalTable_sound h4] at hq
      have hb := quotientSafe BB6.Agent25Raw43E1RE.p43child_root BB6.Agent25Raw43E1RE.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h5 : equalTable e.2 BB6.Agent25Raw43E0RF.p43child = true
    · rw [equalTable_sound h5] at hq
      have hb := quotientSafe BB6.Agent25Raw43E0RF.p43child_root BB6.Agent25Raw43E0RF.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h6 : equalTable e.2 BB6.Agent25Raw43E1LB.p43child = true
    · rw [equalTable_sound h6] at hq
      have hb := quotientSafe BB6.Agent25Raw43E1LB.p43child_root BB6.Agent25Raw43E1LB.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h7 : equalTable e.2 BB6.Agent25Raw43E0RC.p43child = true
    · rw [equalTable_sound h7] at hq
      have hb := quotientSafe BB6.Agent25Raw43E0RC.p43child_root BB6.Agent25Raw43E0RC.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h8 : equalTable e.2 BB6.Agent25Raw43E0LF.p43child = true
    · rw [equalTable_sound h8] at hq
      have hb := quotientSafe BB6.Agent25Raw43E0LF.p43child_root BB6.Agent25Raw43E0LF.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h9 : equalTable e.2 BB6.Agent25Raw43E1LA.p43child = true
    · rw [equalTable_sound h9] at hq
      have hb := quotientSafe BB6.Agent25Raw43E1LA.p43child_root BB6.Agent25Raw43E1LA.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h10 : equalTable e.2 BB6.Agent25Raw43E1LE.p43child = true
    · rw [equalTable_sound h10] at hq
      have hb := quotientSafe BB6.Agent25Raw43E1LE.p43child_root BB6.Agent25Raw43E1LE.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h11 : equalTable e.2 BB6.Agent25Raw43E1RF.p43child = true
    · rw [equalTable_sound h11] at hq
      have hb := quotientSafe BB6.Agent25Raw43E1RF.p43child_root BB6.Agent25Raw43E1RF.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h12 : equalTable e.2 BB6.Agent25Raw43E1LF.p43child = true
    · rw [equalTable_sound h12] at hq
      have hb := quotientSafe BB6.Agent25Raw43E1LF.p43child_root BB6.Agent25Raw43E1LF.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    exact Or.inr ⟨e, by simp [remaining,before,he,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12], hq⟩
theorem cover {B : Nat} (hB : 1713 ≤ B)
    (hRest : ∀ e ∈ remaining, Cover (WeightedBound B) e.2) : Cover (WeightedBound B) parent := by
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
end BB6.Agent25Raw43ParentAll
