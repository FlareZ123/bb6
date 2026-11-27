import Raw43B1LBCut
import Raw43B1LB_C0LAData
import Raw43B1LB_C0LEData
import Raw43B1LB_C0RAData
import Raw43B1LB_C0REData
import Raw43B1LB_C1LAData
import Raw43B1LB_C1LEData
import Raw43B1LB_C1RAData
import Raw43B1LB_C1REData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B1LB
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent8TNFPath
def classified (q : PartialMachine) : Bool :=
  equalTable q BB6.Agent25Raw43B1LB_C0LA.p43child ||
  equalTable q BB6.Agent25Raw43B1LB_C0LE.p43child ||
  equalTable q BB6.Agent25Raw43B1LB_C0RA.p43child ||
  equalTable q BB6.Agent25Raw43B1LB_C0RE.p43child ||
  equalTable q BB6.Agent25Raw43B1LB_C1LA.p43child ||
  equalTable q BB6.Agent25Raw43B1LB_C1LE.p43child ||
  equalTable q BB6.Agent25Raw43B1LB_C1RA.p43child ||
  equalTable q BB6.Agent25Raw43B1LB_C1RE.p43child
theorem classified_all : remaining.all (fun e => classified e.2) = true := by decide
theorem all_quotient (m : Machine) (hm : TNFQuotientCompatible p m) : WeightedBound 289 m := by
  rcases sound m hm with hb | ⟨e,he,hq⟩
  · exact hb
  · have hc := List.all_eq_true.mp classified_all e he
    by_cases h0 : equalTable e.2 BB6.Agent25Raw43B1LB_C0LA.p43child = true
    · rw [equalTable_sound h0] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LB_C0LA.p43child_root BB6.Agent25Raw43B1LB_C0LA.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h1 : equalTable e.2 BB6.Agent25Raw43B1LB_C0LE.p43child = true
    · rw [equalTable_sound h1] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LB_C0LE.p43child_root BB6.Agent25Raw43B1LB_C0LE.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h2 : equalTable e.2 BB6.Agent25Raw43B1LB_C0RA.p43child = true
    · rw [equalTable_sound h2] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LB_C0RA.p43child_root BB6.Agent25Raw43B1LB_C0RA.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h3 : equalTable e.2 BB6.Agent25Raw43B1LB_C0RE.p43child = true
    · rw [equalTable_sound h3] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LB_C0RE.p43child_root BB6.Agent25Raw43B1LB_C0RE.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h4 : equalTable e.2 BB6.Agent25Raw43B1LB_C1LA.p43child = true
    · rw [equalTable_sound h4] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LB_C1LA.p43child_root BB6.Agent25Raw43B1LB_C1LA.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h5 : equalTable e.2 BB6.Agent25Raw43B1LB_C1LE.p43child = true
    · rw [equalTable_sound h5] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LB_C1LE.p43child_root BB6.Agent25Raw43B1LB_C1LE.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h6 : equalTable e.2 BB6.Agent25Raw43B1LB_C1RA.p43child = true
    · rw [equalTable_sound h6] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LB_C1RA.p43child_root BB6.Agent25Raw43B1LB_C1RA.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    by_cases h7 : equalTable e.2 BB6.Agent25Raw43B1LB_C1RE.p43child = true
    · rw [equalTable_sound h7] at hq
      have hb := quotientSafe BB6.Agent25Raw43B1LB_C1RE.p43child_root BB6.Agent25Raw43B1LB_C1RE.all43child m hq
      exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
    simp [classified,h0,h1,h2,h3,h4,h5,h6,h7] at hc
theorem all_completions (m : Machine) (hm : compatible p m) : WeightedBound 289 m :=
  all_quotient m (compatible_quotient hm)
theorem cover {B : Nat} (hB : 289 ≤ B) : Cover (WeightedBound B) p := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans (all_completions m hm k d hk hd) hB
#print axioms classified_all
#print axioms all_completions
#print axioms cover
end BB6.Agent25Raw43B1LB
