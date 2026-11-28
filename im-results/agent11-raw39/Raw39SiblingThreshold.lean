import Raw39TenChildPartial
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
The source-accepted ten-child proof supports any B >= 15125: all siblings
are bounded there and only the A1=1LE child remains. This is a general
usable upper-bound *reduction*, not a whole-cylinder proof.
-/
namespace BB6.Agent11Raw39SiblingThreshold

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent11SemanticChunks
open BB6.Agent11Raw39AcceptedSix (p39 child)

theorem bound_from_oneLE (B : Nat) (hB : 15125 ≤ B)
    (h1 : Bound B (child ⟨true,false,4⟩)) : Bound B p39 := by
  apply BB6.Agent11Raw39AcceptedNine.parent_bound_two B (by omega)
  intro mv hm
  simp only [BB6.Agent11Raw39AcceptedNine.remaining,
    List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact BB6.Agent43Raw391LEBoundLift.mono hB
      BB6.Agent11Raw39TenChild.zeroLE_bound
  · exact h1

theorem cover_from_oneLE (B : Nat) (hB : 15125 ≤ B)
    (h1 : Bound B (child ⟨true,false,4⟩)) :
    Cover (WeightedBound B) p39 :=
  .leaf p39 (bound_from_oneLE B hB h1)

#print axioms bound_from_oneLE
#print axioms cover_from_oneLE

end BB6.Agent11Raw39SiblingThreshold
