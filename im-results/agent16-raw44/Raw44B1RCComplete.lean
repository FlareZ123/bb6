import Raw44B1RCJoinCore
import Raw44Top
import WeightedSymmetry
import Raw44C11LECutAssembled
import Raw44C11RECutAssembled

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw44B1RCJoin
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6Coverage.Agent10ZipAudit BB6.Agent16WeightedSymmetry

theorem new1LE (m : Machine) (hm : compatible (child (some ⟨true,false,4⟩)) m) : WeightedBound 475 m := by
  have he : (child (some ⟨true,false,4⟩)) = BB6.Agent16Raw44C11LECut.parent := tableOK_sound _ _ (by decide +kernel)
  rw [he] at hm
  exact BB6.Agent16Raw44C11LECut.weighted_bound m hm

theorem new1RE (m : Machine) (hm : compatible (child (some ⟨true,true,4⟩)) m) : WeightedBound 155 m := by
  have he : (child (some ⟨true,true,4⟩)) = BB6.Agent16Raw44C11RECut.parent := tableOK_sound _ _ (by decide +kernel)
  rw [he] at hm
  exact BB6.Agent16Raw44C11RECut.weighted_bound m hm

theorem transport0LE (h : ∀ m, compatible (child (some ⟨false,false,4⟩)) m → WeightedBound 373 m) :
    ∀ m, compatible (child (some ⟨false,false,5⟩)) m → WeightedBound 373 m :=
  weighted_cover_transport 373 (swapStates 4 5) (by decide)
    (tableOK_sound _ _ (by decide +kernel)) h

theorem transport0RE (h : ∀ m, compatible (child (some ⟨false,true,4⟩)) m → WeightedBound 211 m) :
    ∀ m, compatible (child (some ⟨false,true,5⟩)) m → WeightedBound 211 m :=
  weighted_cover_transport 211 (swapStates 4 5) (by decide)
    (tableOK_sound _ _ (by decide +kernel)) h

theorem transport1LE (h : ∀ m, compatible (child (some ⟨true,false,4⟩)) m → WeightedBound 475 m) :
    ∀ m, compatible (child (some ⟨true,false,5⟩)) m → WeightedBound 475 m :=
  weighted_cover_transport 475 (swapStates 4 5) (by decide)
    (tableOK_sound _ _ (by decide +kernel)) h

theorem transport1RE (h : ∀ m, compatible (child (some ⟨true,true,4⟩)) m → WeightedBound 155 m) :
    ∀ m, compatible (child (some ⟨true,true,5⟩)) m → WeightedBound 155 m :=
  weighted_cover_transport 155 (swapStates 4 5) (by decide)
    (tableOK_sound _ _ (by decide +kernel)) h

theorem cycle0LB (m : Machine) (hm : compatible (child (some ⟨false,false,1⟩)) m) : WeightedBound 475 m :=
  weighted_never 475 m (zipCycle_sound (child (some ⟨false,false,1⟩)) 49 1 false (5) (by decide) (by decide +kernel) m hm)

theorem cycle0LC (m : Machine) (hm : compatible (child (some ⟨false,false,2⟩)) m) : WeightedBound 475 m :=
  weighted_never 475 m (zipCycle_sound (child (some ⟨false,false,2⟩)) 9 1 false (1) (by decide) (by decide +kernel) m hm)

theorem cycle0LD (m : Machine) (hm : compatible (child (some ⟨false,false,3⟩)) m) : WeightedBound 475 m :=
  weighted_never 475 m (zipCycle_sound (child (some ⟨false,false,3⟩)) 8 1 false (0) (by decide) (by decide +kernel) m hm)

theorem cycle0RB (m : Machine) (hm : compatible (child (some ⟨false,true,1⟩)) m) : WeightedBound 475 m :=
  weighted_never 475 m (zipCycle_sound (child (some ⟨false,true,1⟩)) 7 9 true (1) (by decide) (by decide +kernel) m hm)

theorem cycle0RC (m : Machine) (hm : compatible (child (some ⟨false,true,2⟩)) m) : WeightedBound 475 m :=
  weighted_never 475 m (zipCycle_sound (child (some ⟨false,true,2⟩)) 11 1 false (5) (by decide) (by decide +kernel) m hm)

theorem cycle0RD (m : Machine) (hm : compatible (child (some ⟨false,true,3⟩)) m) : WeightedBound 475 m :=
  weighted_never 475 m (zipCycle_sound (child (some ⟨false,true,3⟩)) 3 11 true (0) (by decide) (by decide +kernel) m hm)

theorem cycle1LA (m : Machine) (hm : compatible (child (some ⟨true,false,0⟩)) m) : WeightedBound 475 m :=
  weighted_never 475 m (zipCycle_sound (child (some ⟨true,false,0⟩)) 6 18 true (0) (by decide) (by decide +kernel) m hm)

theorem cycle1LB (m : Machine) (hm : compatible (child (some ⟨true,false,1⟩)) m) : WeightedBound 475 m :=
  weighted_never 475 m (zipCycle_sound (child (some ⟨true,false,1⟩)) 6 4 true (0) (by decide) (by decide +kernel) m hm)

theorem cycle1LC (m : Machine) (hm : compatible (child (some ⟨true,false,2⟩)) m) : WeightedBound 475 m :=
  weighted_never 475 m (zipCycle_sound (child (some ⟨true,false,2⟩)) 7 5 false (1) (by decide) (by decide +kernel) m hm)

theorem cycle1LD (m : Machine) (hm : compatible (child (some ⟨true,false,3⟩)) m) : WeightedBound 475 m :=
  weighted_never 475 m (zipCycle_sound (child (some ⟨true,false,3⟩)) 8 1 false (0) (by decide) (by decide +kernel) m hm)

theorem cycle1RB (m : Machine) (hm : compatible (child (some ⟨true,true,1⟩)) m) : WeightedBound 475 m :=
  weighted_never 475 m (zipCycle_sound (child (some ⟨true,true,1⟩)) 1 9 true (0) (by decide) (by decide +kernel) m hm)

theorem cycle1RC (m : Machine) (hm : compatible (child (some ⟨true,true,2⟩)) m) : WeightedBound 475 m :=
  weighted_never 475 m (zipCycle_sound (child (some ⟨true,true,2⟩)) 2 8 true (0) (by decide) (by decide +kernel) m hm)

theorem cycle1RD (m : Machine) (hm : compatible (child (some ⟨true,true,3⟩)) m) : WeightedBound 475 m :=
  weighted_never 475 m (zipCycle_sound (child (some ⟨true,true,3⟩)) 10 7 true (2) (by decide) (by decide +kernel) m hm)

/-- Compose the five previously source-accepted representative bounds with
our four new ordinary children, thirteen cycles, and the genuine halt child.
The premises are explicit literal tables: no count-based substitution. -/
theorem complete
    (old0LA : ∀ m, compatible (child (some ⟨false,false,0⟩)) m → WeightedBound 126 m)
    (old0LE : ∀ m, compatible (child (some ⟨false,false,4⟩)) m → WeightedBound 373 m)
    (old0RA : ∀ m, compatible (child (some ⟨false,true,0⟩)) m → WeightedBound 375 m)
    (old0RE : ∀ m, compatible (child (some ⟨false,true,4⟩)) m → WeightedBound 211 m)
    (old1RA : ∀ m, compatible (child (some ⟨true,true,0⟩)) m → WeightedBound 211 m)
    : Cover (WeightedBound 475) parent := by
  apply join 475 (by decide)
  intro mv m hm
  rcases mv with ⟨w,r,q⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · exact weighted_mono (by decide) (old0LA m hm)
  · exact weighted_mono (by decide) (old0RA m hm)
  · exact cycle1LA m hm
  · exact weighted_mono (by decide) (old1RA m hm)
  · exact cycle0LB m hm
  · exact cycle0RB m hm
  · exact cycle1LB m hm
  · exact cycle1RB m hm
  · exact cycle0LC m hm
  · exact cycle0RC m hm
  · exact cycle1LC m hm
  · exact cycle1RC m hm
  · exact cycle0LD m hm
  · exact cycle0RD m hm
  · exact cycle1LD m hm
  · exact cycle1RD m hm
  · exact weighted_mono (by decide) (old0LE m hm)
  · exact weighted_mono (by decide) (old0RE m hm)
  · exact weighted_mono (by decide) (new1LE m hm)
  · exact weighted_mono (by decide) (new1RE m hm)
  · exact weighted_mono (by decide) (transport0LE old0LE m hm)
  · exact weighted_mono (by decide) (transport0RE old0RE m hm)
  · exact weighted_mono (by decide) (transport1LE new1LE m hm)
  · exact weighted_mono (by decide) (transport1RE new1RE m hm)

theorem top_child_eq : BB6.Agent16Raw44Top.child (some ⟨false,true,2⟩) = parent :=
  tableOK_sound _ _ (by decide +kernel)

#print axioms new1LE
#print axioms new1RE
#print axioms complete
#print axioms top_child_eq
end BB6.Agent16Raw44B1RCJoin
