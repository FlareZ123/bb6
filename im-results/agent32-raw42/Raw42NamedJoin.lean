import Raw42CanonicalJoin
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent32Raw42NamedJoin
open BB6Coverage BB6.Agent32Raw42

/-- The twelve canonical B1 children of Raw42, in the exact order induced by
    the finite move enumeration.  The four F-labelled aliases are absent. -/
def namedCanonical : List Move :=
  [⟨false,false,0⟩, ⟨false,true,0⟩, ⟨true,false,0⟩, ⟨true,true,0⟩,
   ⟨false,true,1⟩,  ⟨true,false,1⟩, ⟨true,true,1⟩,
   ⟨true,false,2⟩,
   ⟨false,false,4⟩, ⟨false,true,4⟩, ⟨true,false,4⟩, ⟨true,true,4⟩]

theorem canonical_eq_named :
    BB6.Agent32Raw42CanonicalJoin.canonical = namedCanonical := by
  decide

/-- Lift a certified weighted Cover to any larger weighted bound. -/
theorem lift_cover {b B : Nat} {p : PartialMachine} (hb : b ≤ B)
    (h : Cover (WeightedBound b) p) :
    Cover (WeightedBound B) p := by
  refine Cover.leaf p ?_
  intro m hm k d hk hd
  exact Nat.le_trans (h.sound m hm k d hk hd) hb

/-- Stable named interface for the Raw42 parent join.  This removes all finite
    membership bookkeeping from consumers: proving these twelve exact child
    Covers at one common bound is sufficient for the full Raw42 parent. -/
theorem cover_from_named (B : Nat) (hB : 12 ≤ B)
    (h0LA : Cover (WeightedBound B) (child ⟨false,false,0⟩))
    (h0RA : Cover (WeightedBound B) (child ⟨false,true,0⟩))
    (h1LA : Cover (WeightedBound B) (child ⟨true,false,0⟩))
    (h1RA : Cover (WeightedBound B) (child ⟨true,true,0⟩))
    (h0RB : Cover (WeightedBound B) (child ⟨false,true,1⟩))
    (h1LB : Cover (WeightedBound B) (child ⟨true,false,1⟩))
    (h1RB : Cover (WeightedBound B) (child ⟨true,true,1⟩))
    (h1LC : Cover (WeightedBound B) (child ⟨true,false,2⟩))
    (h0LE : Cover (WeightedBound B) (child ⟨false,false,4⟩))
    (h0RE : Cover (WeightedBound B) (child ⟨false,true,4⟩))
    (h1LE : Cover (WeightedBound B) (child ⟨true,false,4⟩))
    (h1RE : Cover (WeightedBound B) (child ⟨true,true,4⟩)) :
    Cover (WeightedBound B) parent := by
  apply BB6.Agent32Raw42CanonicalJoin.cover B hB
  intro mv hm
  rw [canonical_eq_named] at hm
  simp only [namedCanonical, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact h0LA
  · exact h0RA
  · exact h1LA
  · exact h1RA
  · exact h0RB
  · exact h1LB
  · exact h1RB
  · exact h1LC
  · exact h0LE
  · exact h0RE
  · exact h1LE
  · exact h1RE

#print axioms canonical_eq_named
#print axioms lift_cover
#print axioms cover_from_named
end BB6.Agent32Raw42NamedJoin
