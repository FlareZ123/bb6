import BlockPumpCoverage
import ExceptionalPumps

set_option maxRecDepth 24000
set_option maxHeartbeats 0

namespace BB6.Agent50RecursiveResidual
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent50RootFrontier
open BB6Coverage.Agent50Exceptional

def exceptionalCovered (t : PackedTable) : Bool :=
  decide (t=Nested.table false) || decide (t=Nested.table true) || decide (t=DoubleGrow.table)

theorem exceptionalCovered_never (t : PackedTable) (m : Machine)
    (h : exceptionalCovered t=true) (hm : compatible (unpackTable t) m) : NeverHalts m := by
  have hs : (t=Nested.table false ∨ t=Nested.table true) ∨ t=DoubleGrow.table := by
    simpa only [exceptionalCovered,Bool.or_eq_true,decide_eq_true_eq] using h
  rcases hs with (he|he)|he
  · exact Nested.never false m (by simpa only [he] using hm)
  · exact Nested.never true m (by simpa only [he] using hm)
  · exact DoubleGrow.never m (by simpa only [he] using hm)

def closedSiblingRoster : List PackedTable :=
  pumpedSiblingRoster.filter (fun t => !exceptionalCovered t)

def closedRootRoster : List PackedTable :=
  pumpedRootRoster.filter (fun t => !exceptionalCovered t)

theorem closedSiblingRoster_empty : closedSiblingRoster=[] := by decide
theorem closedRootRoster_count : closedRootRoster.length=124 := by decide

theorem closedRootRoster_sound :
    ∀ m, compatible root m → WeightedBound 400 m ∨
      ∃ q ∈ closedRootRoster, compatible (unpackTable q) m := by
  intro m hm
  rcases pumpedRootRoster_sound m hm with hb | ⟨q,hq,hc⟩
  · exact Or.inl hb
  · cases hg : exceptionalCovered q with
    | true => exact Or.inl (weighted_never 400 m (exceptionalCovered_never q m hg hc))
    | false => exact Or.inr ⟨q,List.mem_filter.mpr ⟨hq,by simp [hg]⟩,hc⟩

/-- All residuals of each of the seventeen exact trees are covered.
    No unresolved leaf or cardinality assumption is used. -/
theorem siblingData_all_weighted (e : CheckedTree) (he : e ∈ siblingData)
    (m : Machine) (hm : compatible (unpackTable e.table) m) : WeightedBound 400 m := by
  rcases e.tree.packed_sound 400 (unpackTable e.table) e.checked m hm with hb | ⟨q,hq,hc⟩
  · exact hb
  · have hmem : q ∈ siblingOpenRoster := List.mem_flatMap.mpr ⟨e,he,hq⟩
    cases hg : growthCovered q with
    | true => exact weighted_never 400 m (growthCovered_never q m hg hc)
    | false =>
      have hmem' : q ∈ siblingFinalRoster := List.mem_filter.mpr ⟨hmem,by simp [hg]⟩
      cases hp : pumpCovered q with
      | true => exact weighted_never 400 m (pumpCovered_never q m hp hc)
      | false =>
        have hmem'' : q ∈ pumpedSiblingRoster := List.mem_filter.mpr ⟨hmem',by simp [hp]⟩
        cases hx : exceptionalCovered q with
        | true => exact weighted_never 400 m (exceptionalCovered_never q m hx hc)
        | false =>
          have hbad : q ∈ closedSiblingRoster := List.mem_filter.mpr ⟨hmem'',by simp [hx]⟩
          rw [closedSiblingRoster_empty] at hbad
          simp at hbad

#print axioms exceptionalCovered_never
#print axioms closedSiblingRoster_empty
#print axioms siblingData_all_weighted
#print axioms closedRootRoster_sound
end BB6.Agent50RecursiveResidual
