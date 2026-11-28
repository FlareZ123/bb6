import Q0151B2AllowedSecond

set_option maxHeartbeats 0

/-!
EXHAUSTIVE exact concrete B2 nested repair classification. For any live
right tape whose first run has length two, its next run can ONLY have
length 1, 4k+4, or 4k+5, k≥0. Every remaining source control branch
cannot occur. The corresponding finite categories are 1,4,5,8; no
abstract bad action is needed to cover a physical successor.

This theorem combines the two-mode residual mask obstruction with the
unbounded source-run classification and is independent of experimental
reachability or the 814-state finite invariant.
-/

namespace BB6.Agent5Q0151B2TailFamilies
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151Category
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151RightWordsComplete
open BB6.Agent5Q0151RunLengthCases
open BB6.Agent5Q0151NestedRightCut
open BB6.Agent5Q0151B2AllowedSecond

theorem cat_four (n : Nat) :
    cat (4*n+4) = if n=0 then 4 else 8 := by
  cases n with
  | zero => decide
  | succ n =>
      have h : ¬ 4 * (n+1) + 4 ≤ 4 := by omega
      have hm : (4*(n+1)+4-1)%4=3 := by omega
      simp [cat,h,hm]

theorem cat_five (n : Nat) : cat (4*n+5) = 5 := by
  have h : ¬ 4*n+5 ≤ 4 := by omega
  simp only [cat,if_neg h]
  omega

theorem b_two_all_nested_families (b : Nat) (rest : List Nat)
    (h : rightType (rightSig (1::b::rest)) ≠ 0) :
    b = 0 ∨ (∃ k, b = 4*k+3) ∨ (∃ k, b = 4*k+4) := by
  have htail : rightType (rightSig (b::rest)) ≠ 0 :=
    live_nonempty_tail 1 b rest h
  have hcases := right_live_length_cases b rest htail
  have hall := b_two_second_allowed b rest h
  rcases hcases with h0 | h1 | h4 | h5 | h6
  · exact Or.inl h0
  · omega
  · exact Or.inr (Or.inl ⟨h4.choose,by omega⟩)
  · exact Or.inr (Or.inr ⟨h5.choose,by omega⟩)
  · omega

theorem b_two_nested_cat (b : Nat) (rest : List Nat)
    (h : rightType (rightSig (1::b::rest)) ≠ 0) :
    cat (b+1) = 1 ∨ cat (b+1) = 4 ∨
    cat (b+1) = 5 ∨ cat (b+1) = 8 := by
  rcases b_two_all_nested_families b rest h with
    h0 | ⟨k,hk⟩ | ⟨k,hk⟩
  · subst b; left; decide
  · subst b
    rw [show 4*k+3+1=4*k+4 by omega,cat_four]
    cases k with
    | zero => exact Or.inr (Or.inl rfl)
    | succ k => exact Or.inr (Or.inr (Or.inr rfl))
  · subst b
    rw [show 4*k+4+1=4*k+5 by omega,cat_five]
    exact Or.inr (Or.inr (Or.inl rfl))

#print axioms cat_four
#print axioms cat_five
#print axioms b_two_all_nested_families
#print axioms b_two_nested_cat
end BB6.Agent5Q0151B2TailFamilies
