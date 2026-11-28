import Q0151RightWordsComplete
import Q0151RunLengthCases

set_option maxHeartbeats 0

/-!
Exhaustive nested-cut soundness for the exceptional B2 source macro.
The finite interpreter first selects the physical run of length two,
then uses a second cut on the remaining right tape. Even for arbitrarily
long concrete run words, the outer word's live mask forces the suffix
live, so BOTH actual concrete cuts are represented in the finite
interpreter's enumerated choices. The theorem is independent of any
finite closure certificate and eliminates the remaining risk that a
nested cut drops a real source successor.
-/

namespace BB6.Agent5Q0151NestedRightCut
open BB6.Agent5Q0151RightWordsComplete
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151Category

theorem live_nonempty_tail (a b : Nat) (rest : List Nat)
    (h : rightType (rightSig (a::b::rest)) ≠ 0) :
    rightType (rightSig (b::rest)) ≠ 0 := by
  have hc : cat (a+1) ≠ 0 := cat_pos a
  have ht : suffixMask (b::rest) ≠ 0 := by
    intro hz
    apply h
    simp [rightSig,rightType,hc,hz,pre_zero]
  change pre (cat (b+1)) (suffixMask rest) ≠ 0 at ht
  simpa [rightSig,rightType,cat_pos b] using ht

theorem nested_cut_second (a b : Nat) (rest : List Nat)
    (h : rightType (rightSig (a::b::rest)) ≠ 0) :
    actualNext (b::rest) ∈ cut (rightSig (b::rest)) :=
  cut_real_next (b::rest) (live_nonempty_tail a b rest h)

theorem b_two_nested (b : Nat) (rest : List Nat)
    (h : rightType (rightSig (1::b::rest)) ≠ 0) :
    (2,rightSig (b::rest)) ∈ cut (rightSig (1::b::rest)) ∧
      actualNext (b::rest) ∈ cut (rightSig (b::rest)) := by
  have hfirst : (2,rightSig (b::rest)) ∈ cut (rightSig (1::b::rest)) := by
    simpa [actualNext,cat] using cut_real_next (1::b::rest) h
  exact ⟨hfirst,nested_cut_second 1 b rest h⟩

#print axioms live_nonempty_tail
#print axioms b_two_nested
end BB6.Agent5Q0151NestedRightCut
