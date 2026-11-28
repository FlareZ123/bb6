import Raw39TenChildPartial

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
All-threshold Raw39 reduction. The 1LE child alone has a checked weighted
attainment of 28311, whereas all ten sibling first-hole branches have
source-accepted weighted upper bounds at most 15125. Thus at *every* natural
weighted threshold, Raw39 is bounded exactly when its 1LE child is bounded.
No complete 1LE upper bound is assumed or asserted.
-/

namespace BB6.Agent11Raw39ThresholdReduction

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent11SemanticChunks
open BB6.Agent11Raw39AcceptedSix (p39 child)
open BB6.Agent43Raw391LEBoundLift (mono)

theorem oneLE_lower_bound (B : Nat)
    (h : Bound B (child ⟨true,false,4⟩)) : 28311 ≤ B := by
  by_cases hc : 28311 ≤ B
  · exact hc
  · exact False.elim
      (BB6.Agent43Raw391LELate.parent_not_bound
        (mono (by omega : B ≤ 28310) h))

/-- An *unconditional equivalence for every finite threshold*, not only 28311.
The RHS remains open as a whole-child upper-bound problem. -/
theorem bound_iff_oneLE (B : Nat) :
    Bound B p39 ↔ Bound B (child ⟨true,false,4⟩) := by
  constructor
  · intro hp m hm k d hk hd
    exact hp m
      (refine_preserves_compat p39 m (0,true)
        (some ⟨true,false,4⟩) (by decide) hm)
      k d hk hd
  · intro h1
    have hB : 28311 ≤ B := oneLE_lower_bound B h1
    apply BB6.Agent11Raw39AcceptedNine.parent_bound_two B (by omega)
    intro mv hm
    simp only [BB6.Agent11Raw39AcceptedNine.remaining,
      List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact mono (by omega : 15125 ≤ B)
        BB6.Agent11Raw39TenChild.zeroLE_bound
    · exact h1

#print axioms oneLE_lower_bound
#print axioms bound_iff_oneLE

end BB6.Agent11Raw39ThresholdReduction
