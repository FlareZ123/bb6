import Raw43B1LACut
import Raw43B1LA_A0LBData
import Raw43B1LA_A0LCData
import Raw43B1LA_A0LDData
import Raw43B1LA_A0LEData
import Raw43B1LA_A0RCData
import Raw43B1LA_A0REData
import Raw43B1LA_A1LBData
import Raw43B1LA_A1LCData
import Raw43B1LA_A1LEData
import Raw43B1LA_A1RCData
import Raw43B1LA_A1REData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B1LA
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent8TNFPath
def residual := refine p (0,true) (some ⟨false,false,0⟩)
def classified (q : PartialMachine) : Bool :=
  equalTable q BB6.Agent25Raw43B1LA_A0LB.p43child ||
  equalTable q BB6.Agent25Raw43B1LA_A0LC.p43child ||
  equalTable q BB6.Agent25Raw43B1LA_A0LD.p43child ||
  equalTable q BB6.Agent25Raw43B1LA_A0LE.p43child ||
  equalTable q BB6.Agent25Raw43B1LA_A0RC.p43child ||
  equalTable q BB6.Agent25Raw43B1LA_A0RE.p43child ||
  equalTable q BB6.Agent25Raw43B1LA_A1LB.p43child ||
  equalTable q BB6.Agent25Raw43B1LA_A1LC.p43child ||
  equalTable q BB6.Agent25Raw43B1LA_A1LE.p43child ||
  equalTable q BB6.Agent25Raw43B1LA_A1RC.p43child ||
  equalTable q BB6.Agent25Raw43B1LA_A1RE.p43child
theorem residual_count : (remaining.filter fun e => !classified e.2).length = 1 := by decide
theorem classified_or_residual : remaining.all (fun e => classified e.2 || equalTable e.2 residual) = true := by decide
theorem reduced (m : Machine) (hm : TNFQuotientCompatible p m) :
    WeightedBound 602 m ∨ TNFQuotientCompatible residual m := by
  rcases sound m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · have hc := List.all_eq_true.mp classified_or_residual e he
    by_cases h0 : equalTable e.2 BB6.Agent25Raw43B1LA_A0LB.p43child = true
    · rw [equalTable_sound h0] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LA_A0LB.p43child_root BB6.Agent25Raw43B1LA_A0LB.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h1 : equalTable e.2 BB6.Agent25Raw43B1LA_A0LC.p43child = true
    · rw [equalTable_sound h1] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LA_A0LC.p43child_root BB6.Agent25Raw43B1LA_A0LC.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h2 : equalTable e.2 BB6.Agent25Raw43B1LA_A0LD.p43child = true
    · rw [equalTable_sound h2] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LA_A0LD.p43child_root BB6.Agent25Raw43B1LA_A0LD.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h3 : equalTable e.2 BB6.Agent25Raw43B1LA_A0LE.p43child = true
    · rw [equalTable_sound h3] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LA_A0LE.p43child_root BB6.Agent25Raw43B1LA_A0LE.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h4 : equalTable e.2 BB6.Agent25Raw43B1LA_A0RC.p43child = true
    · rw [equalTable_sound h4] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LA_A0RC.p43child_root BB6.Agent25Raw43B1LA_A0RC.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h5 : equalTable e.2 BB6.Agent25Raw43B1LA_A0RE.p43child = true
    · rw [equalTable_sound h5] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LA_A0RE.p43child_root BB6.Agent25Raw43B1LA_A0RE.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h6 : equalTable e.2 BB6.Agent25Raw43B1LA_A1LB.p43child = true
    · rw [equalTable_sound h6] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LA_A1LB.p43child_root BB6.Agent25Raw43B1LA_A1LB.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h7 : equalTable e.2 BB6.Agent25Raw43B1LA_A1LC.p43child = true
    · rw [equalTable_sound h7] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LA_A1LC.p43child_root BB6.Agent25Raw43B1LA_A1LC.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h8 : equalTable e.2 BB6.Agent25Raw43B1LA_A1LE.p43child = true
    · rw [equalTable_sound h8] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LA_A1LE.p43child_root BB6.Agent25Raw43B1LA_A1LE.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h9 : equalTable e.2 BB6.Agent25Raw43B1LA_A1RC.p43child = true
    · rw [equalTable_sound h9] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LA_A1RC.p43child_root BB6.Agent25Raw43B1LA_A1RC.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    by_cases h10 : equalTable e.2 BB6.Agent25Raw43B1LA_A1RE.p43child = true
    · rw [equalTable_sound h10] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LA_A1RE.p43child_root BB6.Agent25Raw43B1LA_A1RE.all43child m hq
      exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
    have heq : equalTable e.2 residual = true := by simpa [classified,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10] using hc
    rw [equalTable_sound heq] at hq
    exact Or.inr hq
theorem residual_root : residual initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem cover {B : Nat} (hB : 602 ≤ B) (hR : Cover (WeightedBound B) residual) :
    Cover (WeightedBound B) p := by
  apply Cover.leaf
  intro m hm
  rcases reduced m (compatible_quotient hm) with hb | hr
  · exact fun k d hk hd => Nat.le_trans (hb k d hk hd) hB
  · exact quotientSafe residual_root hR.sound m hr
#print axioms residual_count
#print axioms reduced
#print axioms cover
end BB6.Agent25Raw43B1LA
