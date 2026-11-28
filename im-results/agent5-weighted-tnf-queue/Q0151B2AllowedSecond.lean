import Q0151NestedRightCut

set_option maxHeartbeats 0

/-!
The exceptional B2 source branch splits its right tape after the first
run of length two and makes a nested cut. The abstract interpreter
contains a .bad alternative if the second run has residue 2 or 3 mod 4.
These alternatives are mathematically IMPOSSIBLE for an actually live
concrete right tape, irrespective of finite certificate coverage.

Proof: a residue-2 run maps both-source-mode acceptance into {0,2};
a preceding run of length two maps both of those masks to 0. Residue-3
runs already map to 0. Therefore the second run is necessarily 0 or 1
mod 4 and agrees exactly with the two implemented B2 repair families.
-/

namespace BB6.Agent5Q0151B2AllowedSecond
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151Category
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151RightWordsComplete
open BB6.Agent5Q0151NestedRightCut

theorem pre_mod_two (n t : Nat) (h : n%4=2) :
    pre n t = if maskAccept t 0 then 2 else 0 := by
  have h0 : dnext 0 n = -1 := by simp [dnext,h]
  have h1 : dnext 1 n = 0 := by simp [dnext,h]
  simp [pre,h0,h1,maskAccept]

theorem double_pre_two (n t : Nat) (hn : n%4=2) :
    pre 2 (pre n t) = 0 := by
  rw [pre_mod_two n t hn]
  cases hm : maskAccept t 0 <;> decide

theorem b_two_second_not_even (n : Nat) (rest : List Nat)
    (h : rightType (rightSig (1::n::rest)) ≠ 0) :
    (n+1)%4 ≠ 2 := by
  intro hm
  have hcat : cat (n+1)%4=2 := by rw [cat_mod]; exact hm
  have htype : pre 2 (pre (cat (n+1)) (suffixMask rest)) ≠ 0 := by
    change pre 2 (pre (cat (n+1)) (suffixMask rest)) ≠ 0 at h
    exact h
  exact htype (double_pre_two (cat (n+1)) (suffixMask rest) hcat)

theorem b_two_second_allowed (n : Nat) (rest : List Nat)
    (h : rightType (rightSig (1::n::rest)) ≠ 0) :
    (n+1)%4 = 0 ∨ (n+1)%4 = 1 := by
  have heven := b_two_second_not_even n rest h
  have hthree : (n+1)%4 ≠ 3 := by
    intro hh
    have hc : cat (n+1)%4=3 := by rw [cat_mod]; exact hh
    have htype : pre 2 (pre (cat (n+1)) (suffixMask rest)) ≠ 0 := by
      change pre 2 (pre (cat (n+1)) (suffixMask rest)) ≠ 0 at h
      exact h
    have hp : pre (cat (n+1)) (suffixMask rest) = 0 :=
      pre_mod_three_zero (cat (n+1)) (suffixMask rest) hc
    exact htype (by rw [hp]; decide)
  omega

#print axioms pre_mod_two
#print axioms double_pre_two
#print axioms b_two_second_allowed
end BB6.Agent5Q0151B2AllowedSecond
