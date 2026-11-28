import SparseBlankDelay
set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace BB6.Agent24Raw45Sharp96
open BB6Coverage BB6.Agent13BlankDelay

/-- Literal complete six-state, two-symbol machine, with the E1
    transition halting. One of two symmetric witnesses attaining 96. -/
def witness : Machine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some ⟨true,true,1⟩
  | 0, true  => some ⟨false,false,2⟩
  | 1, false => some ⟨true,true,2⟩
  | 1, true  => some ⟨false,false,0⟩
  | 2, false => some ⟨false,true,3⟩
  | 2, true  => some ⟨false,false,4⟩
  | 3, false => some ⟨true,false,3⟩
  | 3, true  => some ⟨true,true,1⟩
  | 4, false => some ⟨false,false,5⟩
  | 4, true  => none
  | 5, false => some ⟨true,true,5⟩
  | 5, true  => some ⟨false,true,0⟩
  | _,_ => none

/-- 95 ordinary moves from the genuine blank tape, then a
    halting E1 query: 96 steps with the final halt counted. -/
theorem halts_after_95 : HaltsAfter witness 95 := by
  constructor
  · rfl
  · rfl

/-- The initial A0 writes a one, so the blank-entry delay is zero. -/
theorem zero_delay : 0 ∈ delays (zeroNext witness) 0 := by decide

/-- No universal weighted upper bound 95 is possible for this
    literal five-hole Raw45 parent, since this completion scores 96. -/
theorem excludes_bound_95 : ¬ WeightedBound 95 witness := by
  intro h
  have hw := h 95 0 halts_after_95 zero_delay
  omega

#print axioms halts_after_95
#print axioms zero_delay
#print axioms excludes_bound_95
end BB6.Agent24Raw45Sharp96
