import Raw54RootCompose
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false
namespace BB6.Agent8Raw54
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6Coverage.Agent10ZipAudit

/-- The twelve Raw54 E1 child moves not in the four automatic cycles or
    the eight independently source-certified children. -/
def rootRemaining12 : List Move :=
  [⟨false,false,0⟩, ⟨true,false,0⟩, ⟨true,true,0⟩,
   ⟨false,false,1⟩, ⟨true,false,1⟩, ⟨true,true,1⟩,
   ⟨true,false,2⟩,
   ⟨true,true,3⟩,
   ⟨true,false,4⟩,
   ⟨false,false,5⟩, ⟨true,false,5⟩, ⟨true,true,5⟩]

theorem rootRemaining12_length : rootRemaining12.length = 12 := by decide

/-- This logical cut assumes the eight child bounds and exactly twelve
    additional covers. The consuming source bridge must supply all eight
    certified children; the twelve residual premises remain open. -/
theorem root_cover_of_eight_and_remaining12
    (h0LE : ∀ m, compatible (rootChild ⟨false,false,4⟩) m → WeightedBound 39447 m)
    (h0RA : ∀ m, compatible (rootChild ⟨false,true,0⟩) m → WeightedBound 39447 m)
    (h0RB : ∀ m, compatible (rootChild ⟨false,true,1⟩) m → WeightedBound 39447 m)
    (h0RC : ∀ m, compatible (rootChild ⟨false,true,2⟩) m → WeightedBound 39447 m)
    (h0RE : ∀ m, compatible (rootChild ⟨false,true,4⟩) m → WeightedBound 39447 m)
    (h0RF : ∀ m, compatible (rootChild ⟨false,true,5⟩) m → WeightedBound 39447 m)
    (h1RC : ∀ m, compatible (rootChild ⟨true,true,2⟩) m → WeightedBound 39447 m)
    (h1RE : ∀ m, compatible (rootChild ⟨true,true,4⟩) m → WeightedBound 39447 m)
    (hRemaining : ∀ mv, mv ∈ rootRemaining12 →
       ∀ m, compatible (rootChild mv) m → WeightedBound 39447 m) :
    ∀ m, compatible raw54 m → WeightedBound 39447 m := by
  apply root_cover_of_open_children 39447 (by decide)
  intro mv hnc
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  all_goals first
    | exact h0LE
    | exact h0RA
    | exact h0RB
    | exact h0RC
    | exact h0RE
    | exact h0RF
    | exact h1RC
    | exact h1RE
    | exact hRemaining _ (by decide)
    | simp [rootCycle] at hnc

#print axioms rootRemaining12_length
#print axioms root_cover_of_eight_and_remaining12
end BB6.Agent8Raw54
