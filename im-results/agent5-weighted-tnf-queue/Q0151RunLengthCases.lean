import Q0151RightWordsComplete

set_option maxHeartbeats 0

/-!
EXHAUSTIVE original-machine run-length classification, with no finite
simulation assumptions. Every live nonempty right word has a first one-run
length either 1, 2, 4k+4, 4k+5, or 4k+6. The sixth apparent residue
class, 4k+3, has no live successor under the two-mode automaton.
These are exactly the true source-macro families, unbounded in k.
Hence a source-to-abstract refinement need cover these five families,
not arbitrarily many hardcoded observed run lengths.
-/

namespace BB6.Agent5Q0151RunLengthCases
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151Category
open BB6.Agent5Q0151RightWordsComplete
open BB6.Agent5Q0151RightWords

theorem live_length_cases (n : Nat) (t : Nat)
    (h : pre (cat (n+1)) t ≠ 0) :
    n = 0 ∨ n = 1 ∨
    (∃ k, n+1 = 4*k+4) ∨
    (∃ k, n+1 = 4*k+5) ∨
    (∃ k, n+1 = 4*k+6) := by
  have hmod : (n+1)%4 ≠ 3 := by
    intro hm
    have hc : (cat (n+1))%4 = 3 := by rw [cat_mod]; exact hm
    exact h (pre_mod_three_zero (cat (n+1)) t hc)
  by_cases h0 : n = 0
  · exact Or.inl h0
  by_cases h1 : n = 1
  · exact Or.inr (Or.inl h1)
  have hlarge : 3 ≤ n+1 := by omega
  have hm : (n+1)%4 = 0 ∨ (n+1)%4 = 1 ∨ (n+1)%4 = 2 := by omega
  rcases hm with hm | hm | hm
  · refine Or.inr (Or.inr (Or.inl ⟨(n+1)/4-1,?_⟩))
    omega
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨(n+1)/4-1,?_⟩)))
    omega
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨(n+1)/4-1,?_⟩)))
    omega

theorem right_live_length_cases (n : Nat) (rest : List Nat)
    (h : rightType (rightSig (n::rest)) ≠ 0) :
    n = 0 ∨ n = 1 ∨
    (∃ k, n+1 = 4*k+4) ∨
    (∃ k, n+1 = 4*k+5) ∨
    (∃ k, n+1 = 4*k+6) := by
  have hc : cat (n+1) ≠ 0 := cat_pos n
  have hh : pre (cat (n+1)) (suffixMask rest) ≠ 0 := by
    simpa [rightType,rightSig,hc] using h
  exact live_length_cases n (suffixMask rest) hh

#print axioms live_length_cases
#print axioms right_live_length_cases
end BB6.Agent5Q0151RunLengthCases
