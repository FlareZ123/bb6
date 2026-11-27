import Raw43B1LECut
import Raw43B1LE_E0LAData
import Raw43B1LE_E0LBData
import Raw43B1LE_E0LCData
import Raw43B1LE_E0LDData
import Raw43B1LE_E0LEData
import Raw43B1LE_E0LFData
import Raw43B1LE_E0RAData
import Raw43B1LE_E0RCData
import Raw43B1LE_E0REData
import Raw43B1LE_E0RFData
import Raw43B1LE_E1LAData
import Raw43B1LE_E1LBData
import Raw43B1LE_E1LCData
import Raw43B1LE_E1LEData
import Raw43B1LE_E1LFData
import Raw43B1LE_E1RAData
import Raw43B1LE_E1RBData
import Raw43B1LE_E1RCData
import Raw43B1LE_E1REData
import Raw43B1LE_E1RFData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B1LE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent8TNFPath

def classified (q : PartialMachine) : Bool :=
  equalTable q BB6.Agent25Raw43B1LE_E0LA.p43child ||
  equalTable q BB6.Agent25Raw43B1LE_E0LB.p43child ||
  equalTable q BB6.Agent25Raw43B1LE_E0LC.p43child ||
  equalTable q BB6.Agent25Raw43B1LE_E0LD.p43child ||
  equalTable q BB6.Agent25Raw43B1LE_E0LE.p43child ||
  equalTable q BB6.Agent25Raw43B1LE_E0LF.p43child ||
  equalTable q BB6.Agent25Raw43B1LE_E0RA.p43child ||
  equalTable q BB6.Agent25Raw43B1LE_E0RC.p43child ||
  equalTable q BB6.Agent25Raw43B1LE_E0RE.p43child ||
  equalTable q BB6.Agent25Raw43B1LE_E0RF.p43child ||
  equalTable q BB6.Agent25Raw43B1LE_E1LA.p43child ||
  equalTable q BB6.Agent25Raw43B1LE_E1LB.p43child ||
  equalTable q BB6.Agent25Raw43B1LE_E1LC.p43child ||
  equalTable q BB6.Agent25Raw43B1LE_E1LE.p43child ||
  equalTable q BB6.Agent25Raw43B1LE_E1LF.p43child ||
  equalTable q BB6.Agent25Raw43B1LE_E1RA.p43child ||
  equalTable q BB6.Agent25Raw43B1LE_E1RB.p43child ||
  equalTable q BB6.Agent25Raw43B1LE_E1RC.p43child ||
  equalTable q BB6.Agent25Raw43B1LE_E1RE.p43child ||
  equalTable q BB6.Agent25Raw43B1LE_E1RF.p43child

theorem classified_all : remaining.all (fun e => classified e.2) = true := by decide

theorem all_quotient (m : Machine) (hm : TNFQuotientCompatible p m) : WeightedBound 11292 m := by
  rcases sound m hm with hb | ⟨e,he,hq⟩
  · exact hb
  · have hc := List.all_eq_true.mp classified_all e he
    by_cases h0 : equalTable e.2 BB6.Agent25Raw43B1LE_E0LA.p43child = true
    · rw [equalTable_sound h0] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LE_E0LA.p43child_root BB6.Agent25Raw43B1LE_E0LA.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h1 : equalTable e.2 BB6.Agent25Raw43B1LE_E0LB.p43child = true
    · rw [equalTable_sound h1] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LE_E0LB.p43child_root BB6.Agent25Raw43B1LE_E0LB.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h2 : equalTable e.2 BB6.Agent25Raw43B1LE_E0LC.p43child = true
    · rw [equalTable_sound h2] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LE_E0LC.p43child_root BB6.Agent25Raw43B1LE_E0LC.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h3 : equalTable e.2 BB6.Agent25Raw43B1LE_E0LD.p43child = true
    · rw [equalTable_sound h3] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LE_E0LD.p43child_root BB6.Agent25Raw43B1LE_E0LD.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h4 : equalTable e.2 BB6.Agent25Raw43B1LE_E0LE.p43child = true
    · rw [equalTable_sound h4] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LE_E0LE.p43child_root BB6.Agent25Raw43B1LE_E0LE.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h5 : equalTable e.2 BB6.Agent25Raw43B1LE_E0LF.p43child = true
    · rw [equalTable_sound h5] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LE_E0LF.p43child_root BB6.Agent25Raw43B1LE_E0LF.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h6 : equalTable e.2 BB6.Agent25Raw43B1LE_E0RA.p43child = true
    · rw [equalTable_sound h6] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LE_E0RA.p43child_root BB6.Agent25Raw43B1LE_E0RA.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h7 : equalTable e.2 BB6.Agent25Raw43B1LE_E0RC.p43child = true
    · rw [equalTable_sound h7] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LE_E0RC.p43child_root BB6.Agent25Raw43B1LE_E0RC.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h8 : equalTable e.2 BB6.Agent25Raw43B1LE_E0RE.p43child = true
    · rw [equalTable_sound h8] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LE_E0RE.p43child_root BB6.Agent25Raw43B1LE_E0RE.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h9 : equalTable e.2 BB6.Agent25Raw43B1LE_E0RF.p43child = true
    · rw [equalTable_sound h9] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LE_E0RF.p43child_root BB6.Agent25Raw43B1LE_E0RF.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h10 : equalTable e.2 BB6.Agent25Raw43B1LE_E1LA.p43child = true
    · rw [equalTable_sound h10] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LE_E1LA.p43child_root BB6.Agent25Raw43B1LE_E1LA.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h11 : equalTable e.2 BB6.Agent25Raw43B1LE_E1LB.p43child = true
    · rw [equalTable_sound h11] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LE_E1LB.p43child_root BB6.Agent25Raw43B1LE_E1LB.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h12 : equalTable e.2 BB6.Agent25Raw43B1LE_E1LC.p43child = true
    · rw [equalTable_sound h12] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LE_E1LC.p43child_root BB6.Agent25Raw43B1LE_E1LC.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h13 : equalTable e.2 BB6.Agent25Raw43B1LE_E1LE.p43child = true
    · rw [equalTable_sound h13] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LE_E1LE.p43child_root BB6.Agent25Raw43B1LE_E1LE.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h14 : equalTable e.2 BB6.Agent25Raw43B1LE_E1LF.p43child = true
    · rw [equalTable_sound h14] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LE_E1LF.p43child_root BB6.Agent25Raw43B1LE_E1LF.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h15 : equalTable e.2 BB6.Agent25Raw43B1LE_E1RA.p43child = true
    · rw [equalTable_sound h15] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LE_E1RA.p43child_root BB6.Agent25Raw43B1LE_E1RA.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h16 : equalTable e.2 BB6.Agent25Raw43B1LE_E1RB.p43child = true
    · rw [equalTable_sound h16] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LE_E1RB.p43child_root BB6.Agent25Raw43B1LE_E1RB.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h17 : equalTable e.2 BB6.Agent25Raw43B1LE_E1RC.p43child = true
    · rw [equalTable_sound h17] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LE_E1RC.p43child_root BB6.Agent25Raw43B1LE_E1RC.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h18 : equalTable e.2 BB6.Agent25Raw43B1LE_E1RE.p43child = true
    · rw [equalTable_sound h18] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LE_E1RE.p43child_root BB6.Agent25Raw43B1LE_E1RE.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h19 : equalTable e.2 BB6.Agent25Raw43B1LE_E1RF.p43child = true
    · rw [equalTable_sound h19] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LE_E1RF.p43child_root BB6.Agent25Raw43B1LE_E1RF.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    simp [classified,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19] at hc

theorem all_completions (m : Machine) (hm : compatible p m) : WeightedBound 11292 m :=
  all_quotient m (compatible_quotient hm)

theorem cover {B : Nat} (hB : 11292 ≤ B) : Cover (WeightedBound B) p := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans (all_completions m hm k d hk hd) hB

#print axioms classified_all
#print axioms all_completions
#print axioms cover
end BB6.Agent25Raw43B1LE
