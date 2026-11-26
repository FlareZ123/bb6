import RectCover
import Raw10BoxCore
import Box18to24Source
import Box8Closure
import Raw10FixedLeaves

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent49Raw10RefinedCut
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box
open BB6.Agent49BoxBridge BB6.Agent13CrossRouteHeldLeaf109
open BB6.Agent50RootFrontier

abbrev RBox := Box Slot Transition

/-- Same source side, held, cycle and halt tables used in the expanded
    residual. Importing the canonical78/77 roster is unnecessary here. -/
def cuts : List PartialMachine :=
  sideTables ++ [held, BB6.Agent13Raw10FixedLeaves.cycleTable,
    BB6.Agent13Raw10FixedLeaves.haltTable]

def refined : List RBox := remainder firstOneB0_1LC cuts

def accepted : List RBox :=
  BB6.Agent49Box18to24.closedRows.map BB6.Agent49Box18to24.rect ++
    [raw10Remainder[8]!]

def candidate : List RBox :=
  accepted ++ [raw10Remainder[16]!, raw10Remainder[17]!]

def isCovered (cs : List RBox) (r : RBox) : Bool :=
  BB6.RectCover.covered slots cs r

def openBoxes (cs : List RBox) : List RBox :=
  refined.filter fun r => !isCovered cs r

theorem refined_count : refined.length = 41 := by decide +kernel
theorem accepted_open_count : (openBoxes accepted).length = 33 := by decide +kernel
theorem candidate_open_count : (openBoxes candidate).length = 31 := by decide +kernel

private theorem liftBound {b B : Nat} (h : b ≤ B) (m : Machine)
    (hm : WeightedBound b m) : WeightedBound B m := by
  intro k d hk hd
  exact Nat.le_trans (hm k d hk hd) h

theorem accepted_bounds (B : Nat) (hB : 7014 ≤ B) :
    ∀ r ∈ accepted, ∀ m : Machine, Fits r m → WeightedBound B m := by
  intro r hr m hm
  change r ∈ (BB6.Agent49Box18to24.closedRows.map
    BB6.Agent49Box18to24.rect ++ [raw10Remainder[8]!]) at hr
  rcases List.mem_append.mp hr with hs | ht
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
    exact liftBound (by omega : 598 ≤ B) m
      (BB6.Agent49Box18to24.rectBound a ha m hm)
  · have he : r = raw10Remainder[8]! := by simpa using ht
    subst r
    exact liftBound (by omega : 38 ≤ B) m
      (BB6.Agent49Box8.original_box8_bound m hm)

theorem candidate_bounds (B : Nat) (hB : 7376 ≤ B)
    (bound16 : ∀ m : Machine, Fits raw10Remainder[16]! m → WeightedBound 7376 m)
    (bound17 : ∀ m : Machine, Fits raw10Remainder[17]! m → WeightedBound 7014 m) :
    ∀ r ∈ candidate, ∀ m : Machine, Fits r m → WeightedBound B m := by
  intro r hr m hm
  change r ∈ accepted ++ [raw10Remainder[16]!, raw10Remainder[17]!] at hr
  rcases List.mem_append.mp hr with hs | ht
  · exact accepted_bounds B (by omega) r hs m hm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with he | he
    · subst r
      exact liftBound hB m (bound16 m hm)
    · subst r
      exact liftBound (by omega : 7014 ≤ B) m (bound17 m hm)

/-- Generic exact parent consumer; the held leaf remains explicit.
    All refined boxes not contained in a certified box must be covered. -/
def parentCover (B : Nat) (hB : 7014 ≤ B) (cs : List RBox)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hClosed : ∀ r ∈ cs, ∀ m : Machine, Fits r m → WeightedBound B m)
    (hOpen : ∀ r ∈ openBoxes cs, ∀ m : Machine, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC := by
  apply coverFromRemainder B firstOneB0_1LC cuts
  · intro q hq m hm
    change q ∈ sideTables ++ [held, BB6.Agent13Raw10FixedLeaves.cycleTable,
      BB6.Agent13Raw10FixedLeaves.haltTable] at hq
    rcases List.mem_append.mp hq with hs | ht
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hs
      exact liftBound hB m (b0_1lcSideWitnesses_safe w hw m hm)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact hHeld m hm
      · exact (BB6.Agent13Raw10FixedLeaves.cycle_cover B).sound m hm
      · exact liftBound (by omega : 8 ≤ B) m
          (BB6.Agent13Raw10FixedLeaves.halt_cover.sound m hm)
  · change ∀ r ∈ refined, ∀ m : Machine, Fits r m → WeightedBound B m
    apply BB6.RectCover.consume slots slots_complete cs refined (WeightedBound B) hClosed
    intro r hr hfalse m hm
    have hmem : r ∈ openBoxes cs := by
      apply List.mem_filter.mpr
      exact ⟨hr, by simp [isCovered, hfalse]⟩
    exact hOpen r hmem m hm

def parentCover33 (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ r ∈ openBoxes accepted, ∀ m : Machine, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  parentCover B hB accepted hHeld (accepted_bounds B hB) hOpen

/-- No source acceptance for 16/17 is assumed: their exact weighted bounds
    are separate premises until the two original-source audits pass. -/
def parentCover31 (B : Nat) (hB : 7376 ≤ B)
    (bound16 : ∀ m : Machine, Fits raw10Remainder[16]! m → WeightedBound 7376 m)
    (bound17 : ∀ m : Machine, Fits raw10Remainder[17]! m → WeightedBound 7014 m)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ r ∈ openBoxes candidate, ∀ m : Machine, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  parentCover B (by omega) candidate hHeld (candidate_bounds B hB bound16 bound17) hOpen

#print axioms refined_count
#print axioms accepted_open_count
#print axioms candidate_open_count
#print axioms parentCover33
#print axioms parentCover31
end BB6.Agent49Raw10RefinedCut
