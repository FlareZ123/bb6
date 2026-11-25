import DepthEightSiblingCoverage
import DepthEightGrowth17

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50RecursiveResidual
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent50RootFrontier
open BB6.Agent7DepthEightGrowth17

/-- Every entry has an explicit arbitrary-tail sweep induction. -/
def growth17Leaves : List FARLeaf := [
  ⟨M1.table, M1.never⟩,
  ⟨M2.table, M2.never⟩,
  ⟨M3.table, M3.never⟩,
  ⟨M4.table, M4.never⟩,
  ⟨M5.table, M5.never⟩,
  ⟨M6.table, M6.never⟩,
  ⟨M7.table, M7.never⟩,
  ⟨M8.table, M8.never⟩,
  ⟨M9.table, M9.never⟩,
  ⟨M10.table, M10.never⟩,
  ⟨M11.table, M11.never⟩,
  ⟨M12.table, M12.never⟩,
  ⟨M13.table, M13.never⟩,
  ⟨M14.table, M14.never⟩,
  ⟨M15.table, M15.never⟩,
  ⟨M16.table, M16.never⟩,
  ⟨M17.table, M17.never⟩
]

def growth17Covered (t : PackedTable) : Bool :=
  growth17Leaves.any (fun leaf => decide (packTable leaf.val = t))

theorem growth17Covered_never (t : PackedTable) (m : Machine)
    (h : growth17Covered t = true) (hm : compatible (unpackTable t) m) :
    NeverHalts m := by
  obtain ⟨leaf,_,he⟩ := List.any_eq_true.mp h
  have ht : packTable leaf.val = t := of_decide_eq_true he
  exact leaf.property m (by simpa only [← ht,unpack_packTable] using hm)

/-- Check the exact table identities against the actual source-computed residuals. -/
theorem growth17_closes_siblings :
    siblingFinalRoster.all growth17Covered = true := by decide

theorem growth17_no_extras :
    ∀ leaf ∈ growth17Leaves, packTable leaf.val ∈ siblingFinalRoster := by decide

theorem siblingFinalRoster_never (t : PackedTable) (ht : t ∈ siblingFinalRoster)
    (m : Machine) (hm : compatible (unpackTable t) m) : NeverHalts m :=
  growth17Covered_never t m (List.all_eq_true.mp growth17_closes_siblings t ht) hm

def closedSiblingRootRoster : List PackedTable :=
  finalRootRoster.filter (fun t => !growth17Covered t)

theorem closedSiblingRootRoster_sound :
    ∀ m, compatible root m → WeightedBound 400 m ∨
      ∃ q ∈ closedSiblingRootRoster, compatible (unpackTable q) m := by
  intro m hm
  rcases finalRootRoster_sound m hm with hb | ⟨q,hq,hc⟩
  · exact Or.inl hb
  · cases hg : growth17Covered q with
    | true => exact Or.inl (weighted_never 400 m (growth17Covered_never q m hg hc))
    | false => exact Or.inr ⟨q,List.mem_filter.mpr ⟨hq,by simp [hg]⟩,hc⟩

theorem siblingFinalRoster_closed :
    (siblingFinalRoster.filter (fun t => !growth17Covered t)).length = 0 := by decide

theorem closedSiblingRootRoster_count : closedSiblingRootRoster.length = 124 := by decide

#print axioms growth17_closes_siblings
#print axioms growth17_no_extras
#print axioms siblingFinalRoster_never
#print axioms closedSiblingRootRoster_sound
#print axioms siblingFinalRoster_closed
#print axioms closedSiblingRootRoster_count

end BB6.Agent50RecursiveResidual
