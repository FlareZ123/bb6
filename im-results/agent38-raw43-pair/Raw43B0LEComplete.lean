import Raw43B0LEExpanded
import Raw43B0LE_E1LAData
import Raw43B0LE_E1LBData
import Raw43B0LE_E1LFData
import Raw43B0LE_E1RFData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent38Raw43B0LEComplete
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
  BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
  BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent8TNFPath
  BB6.Agent25Raw43B0LE

def classified (q : PartialMachine) : Bool :=
  equalTable q BB6.Agent25Raw43B0LE_E1LA.p43child ||
  equalTable q BB6.Agent25Raw43B0LE_E1LB.p43child ||
  equalTable q BB6.Agent25Raw43B0LE_E1LF.p43child ||
  equalTable q BB6.Agent25Raw43B0LE_E1RF.p43child

theorem classified_all :
    BB6.Agent25Raw43B0LE.expandedResiduals.all (fun e => classified e.2) = true := by
  decide

theorem all_quotient (m : Machine)
    (hm : TNFQuotientCompatible BB6.Agent25Raw43B0LE.p m) :
    WeightedBound 3466 m := by
  rcases BB6.Agent25Raw43B0LE.expandedReduced m hm with hb | ⟨e,he,hq⟩
  · exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
  · have hc := List.all_eq_true.mp classified_all e he
    by_cases h0 : equalTable e.2 BB6.Agent25Raw43B0LE_E1LA.p43child = true
    · rw [equalTable_sound h0] at hq
      have hb := quotientSafe BB6.Agent25Raw43B0LE_E1LA.p43child_root
        BB6.Agent25Raw43B0LE_E1LA.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h1 : equalTable e.2 BB6.Agent25Raw43B0LE_E1LB.p43child = true
    · rw [equalTable_sound h1] at hq
      have hb := quotientSafe BB6.Agent25Raw43B0LE_E1LB.p43child_root
        BB6.Agent25Raw43B0LE_E1LB.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h2 : equalTable e.2 BB6.Agent25Raw43B0LE_E1LF.p43child = true
    · rw [equalTable_sound h2] at hq
      have hb := quotientSafe BB6.Agent25Raw43B0LE_E1LF.p43child_root
        BB6.Agent25Raw43B0LE_E1LF.all43child m hq
      exact hb
    by_cases h3 : equalTable e.2 BB6.Agent25Raw43B0LE_E1RF.p43child = true
    · rw [equalTable_sound h3] at hq
      have hb := quotientSafe BB6.Agent25Raw43B0LE_E1RF.p43child_root
        BB6.Agent25Raw43B0LE_E1RF.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    simp [classified,h0,h1,h2,h3] at hc

theorem all_completions (m : Machine)
    (hm : compatible BB6.Agent25Raw43B0LE.p m) :
    WeightedBound 3466 m :=
  all_quotient m (compatible_quotient hm)

theorem cover {B : Nat} (hB : 3466 ≤ B) :
    Cover (WeightedBound B) BB6.Agent25Raw43B0LE.p := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans (all_completions m hm k d hk hd) hB

#print axioms classified_all
#print axioms all_completions
#print axioms cover
end BB6.Agent38Raw43B0LEComplete
