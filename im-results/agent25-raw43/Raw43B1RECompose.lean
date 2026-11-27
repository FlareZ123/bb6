import Raw43B1RECut
import Raw43B1RE_E10LAData
import Raw43B1RE_E10LBData
import Raw43B1RE_E10LCData
import Raw43B1RE_E10LEData
import Raw43B1RE_E10LFData
import Raw43B1RE_E10RCData
import Raw43B1RE_E10REData
import Raw43B1RE_E10RFData
import Raw43B1RE_E11LAData
import Raw43B1RE_E11LCData
import Raw43B1RE_E11LDData
import Raw43B1RE_E11LEData
import Raw43B1RE_E11LFData
import Raw43B1RE_E11RDData
import Raw43B1RE_E11REData
import Raw43B1RE_E11RFData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B1RE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent8TNFPath

def classified (q : PartialMachine) : Bool :=
  equalTable q BB6.Agent25Raw43B1RE_E10LA.p43child ||
  equalTable q BB6.Agent25Raw43B1RE_E10LB.p43child ||
  equalTable q BB6.Agent25Raw43B1RE_E10LC.p43child ||
  equalTable q BB6.Agent25Raw43B1RE_E10LE.p43child ||
  equalTable q BB6.Agent25Raw43B1RE_E10LF.p43child ||
  equalTable q BB6.Agent25Raw43B1RE_E10RC.p43child ||
  equalTable q BB6.Agent25Raw43B1RE_E10RE.p43child ||
  equalTable q BB6.Agent25Raw43B1RE_E10RF.p43child ||
  equalTable q BB6.Agent25Raw43B1RE_E11LA.p43child ||
  equalTable q BB6.Agent25Raw43B1RE_E11LC.p43child ||
  equalTable q BB6.Agent25Raw43B1RE_E11LD.p43child ||
  equalTable q BB6.Agent25Raw43B1RE_E11LE.p43child ||
  equalTable q BB6.Agent25Raw43B1RE_E11LF.p43child ||
  equalTable q BB6.Agent25Raw43B1RE_E11RD.p43child ||
  equalTable q BB6.Agent25Raw43B1RE_E11RE.p43child ||
  equalTable q BB6.Agent25Raw43B1RE_E11RF.p43child

theorem classified_all : remaining.all (fun e => classified e.2) = true := by decide

theorem all_quotient (m : Machine) (hm : TNFQuotientCompatible p m) : WeightedBound 4044 m := by
  rcases sound m hm with hb | ⟨e,he,hq⟩
  · exact hb
  · have hc := List.all_eq_true.mp classified_all e he
    by_cases h0 : equalTable e.2 BB6.Agent25Raw43B1RE_E10LA.p43child = true
    · rw [equalTable_sound h0] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1RE_E10LA.p43child_root BB6.Agent25Raw43B1RE_E10LA.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h1 : equalTable e.2 BB6.Agent25Raw43B1RE_E10LB.p43child = true
    · rw [equalTable_sound h1] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1RE_E10LB.p43child_root BB6.Agent25Raw43B1RE_E10LB.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h2 : equalTable e.2 BB6.Agent25Raw43B1RE_E10LC.p43child = true
    · rw [equalTable_sound h2] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1RE_E10LC.p43child_root BB6.Agent25Raw43B1RE_E10LC.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h3 : equalTable e.2 BB6.Agent25Raw43B1RE_E10LE.p43child = true
    · rw [equalTable_sound h3] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1RE_E10LE.p43child_root BB6.Agent25Raw43B1RE_E10LE.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h4 : equalTable e.2 BB6.Agent25Raw43B1RE_E10LF.p43child = true
    · rw [equalTable_sound h4] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1RE_E10LF.p43child_root BB6.Agent25Raw43B1RE_E10LF.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h5 : equalTable e.2 BB6.Agent25Raw43B1RE_E10RC.p43child = true
    · rw [equalTable_sound h5] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1RE_E10RC.p43child_root BB6.Agent25Raw43B1RE_E10RC.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h6 : equalTable e.2 BB6.Agent25Raw43B1RE_E10RE.p43child = true
    · rw [equalTable_sound h6] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1RE_E10RE.p43child_root BB6.Agent25Raw43B1RE_E10RE.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h7 : equalTable e.2 BB6.Agent25Raw43B1RE_E10RF.p43child = true
    · rw [equalTable_sound h7] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1RE_E10RF.p43child_root BB6.Agent25Raw43B1RE_E10RF.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h8 : equalTable e.2 BB6.Agent25Raw43B1RE_E11LA.p43child = true
    · rw [equalTable_sound h8] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1RE_E11LA.p43child_root BB6.Agent25Raw43B1RE_E11LA.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h9 : equalTable e.2 BB6.Agent25Raw43B1RE_E11LC.p43child = true
    · rw [equalTable_sound h9] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1RE_E11LC.p43child_root BB6.Agent25Raw43B1RE_E11LC.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h10 : equalTable e.2 BB6.Agent25Raw43B1RE_E11LD.p43child = true
    · rw [equalTable_sound h10] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1RE_E11LD.p43child_root BB6.Agent25Raw43B1RE_E11LD.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h11 : equalTable e.2 BB6.Agent25Raw43B1RE_E11LE.p43child = true
    · rw [equalTable_sound h11] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1RE_E11LE.p43child_root BB6.Agent25Raw43B1RE_E11LE.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h12 : equalTable e.2 BB6.Agent25Raw43B1RE_E11LF.p43child = true
    · rw [equalTable_sound h12] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1RE_E11LF.p43child_root BB6.Agent25Raw43B1RE_E11LF.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h13 : equalTable e.2 BB6.Agent25Raw43B1RE_E11RD.p43child = true
    · rw [equalTable_sound h13] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1RE_E11RD.p43child_root BB6.Agent25Raw43B1RE_E11RD.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h14 : equalTable e.2 BB6.Agent25Raw43B1RE_E11RE.p43child = true
    · rw [equalTable_sound h14] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1RE_E11RE.p43child_root BB6.Agent25Raw43B1RE_E11RE.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h15 : equalTable e.2 BB6.Agent25Raw43B1RE_E11RF.p43child = true
    · rw [equalTable_sound h15] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1RE_E11RF.p43child_root BB6.Agent25Raw43B1RE_E11RF.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    simp [classified,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15] at hc

theorem all_completions (m : Machine) (hm : compatible p m) : WeightedBound 4044 m :=
  all_quotient m (compatible_quotient hm)

theorem cover {B : Nat} (hB : 4044 ≤ B) : Cover (WeightedBound B) p := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans (all_completions m hm k d hk hd) hB

#print axioms classified_all
#print axioms all_completions
#print axioms cover
end BB6.Agent25Raw43B1RE
