import DepthEightSiblingCoverage
import BlockPumpData1
import BlockPumpData2
import BlockPumpData3
import BlockPumpData4

set_option maxRecDepth 24000
set_option maxHeartbeats 0

namespace BB6.Agent50RecursiveResidual
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent50RootFrontier
open BB6Coverage.Agent50Pump

def pumpRoster : List CheckedPump :=
  pumpRoster1 ++ pumpRoster2 ++ pumpRoster3 ++ pumpRoster4

def pumpCovered (t : PackedTable) : Bool :=
  pumpRoster.any (fun w => decide (w.table=t))

theorem pumpCovered_never (t : PackedTable) (m : Machine)
    (h : pumpCovered t=true) (hm : compatible (unpackTable t) m) : NeverHalts m := by
  obtain ⟨w,hw,he⟩ := List.any_eq_true.mp h
  have ht : w.table=t := of_decide_eq_true he
  exact w.never m (by simpa only [ht] using hm)

def pumpedRootRoster : List PackedTable :=
  finalRootRoster.filter (fun t => !pumpCovered t)

def pumpedSiblingRoster : List PackedTable :=
  siblingFinalRoster.filter (fun t => !pumpCovered t)

theorem pumpedRootRoster_sound :
    ∀ m, compatible root m → WeightedBound 400 m ∨
      ∃ q ∈ pumpedRootRoster, compatible (unpackTable q) m := by
  intro m hm
  rcases finalRootRoster_sound m hm with hb | ⟨q,hq,hc⟩
  · exact Or.inl hb
  · cases hg : pumpCovered q with
    | true => exact Or.inl (weighted_never 400 m (pumpCovered_never q m hg hc))
    | false => exact Or.inr ⟨q,List.mem_filter.mpr ⟨hq,by simp [hg]⟩,hc⟩

theorem pumpRoster_count : pumpRoster.length=98 := by decide
theorem pumpedSiblingRoster_count : pumpedSiblingRoster.length=3 := by decide
theorem pumpedSiblingRoster_mass : rawMass pumpedSiblingRoster=75 := by decide
theorem pumpedRootRoster_count : pumpedRootRoster.length=127 := by decide

#print axioms pumpCovered_never
#print axioms pumpedRootRoster_sound
#print axioms pumpedSiblingRoster_mass

end BB6.Agent50RecursiveResidual
