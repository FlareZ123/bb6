import Q0151Category
import Q0151FiniteModel

set_option maxHeartbeats 0
namespace BB6.Agent5Q0151RunClasses
open BB6.Agent5Q0151Category
open BB6.Agent5Q0151FiniteModel

/-!
Inversion of the finite run categories into the *exact* arbitrary source
macro lengths. This bridges the abstract right-run categories 1/2/4/5/6/8
back to the positive-length primitive-machine macro theorems.
-/

theorem small_of_cat_small (n c : Nat)
    (hc : cat n = c) (hsmall : c ≤ 4) : n ≤ 4 := by
  by_contra hn
  have hlarge : 5 ≤ n := by omega
  have hout := cat_large n hlarge
  omega

theorem cat_one (n : Nat) (h : cat n = 1) : n = 1 := by
  have hs := small_of_cat_small n 1 h (by omega)
  rw [cat_small n hs] at h
  exact h

theorem cat_two (n : Nat) (h : cat n = 2) : n = 2 := by
  have hs := small_of_cat_small n 2 h (by omega)
  rw [cat_small n hs] at h
  exact h

theorem cat_four (n : Nat) (h : cat n = 4) : n = 4 := by
  have hs := small_of_cat_small n 4 h (by omega)
  rw [cat_small n hs] at h
  exact h

theorem cat_five (n : Nat) (h : cat n = 5) :
    ∃ k, n = 4*k + 5 := by
  have hn : ¬ n ≤ 4 := by
    intro hs
    have hh := cat_small n hs
    omega
  have hm : (n-1)%4 = 0 := by
    simp only [cat,if_neg hn] at h
    omega
  refine ⟨(n-5)/4,?_⟩
  omega

theorem cat_six (n : Nat) (h : cat n = 6) :
    ∃ k, n = 4*k + 6 := by
  have hn : ¬ n ≤ 4 := by
    intro hs
    have hh := cat_small n hs
    omega
  have hm : (n-1)%4 = 1 := by
    simp only [cat,if_neg hn] at h
    omega
  refine ⟨(n-6)/4,?_⟩
  omega

theorem cat_eight (n : Nat) (h : cat n = 8) :
    ∃ k, n = 4*k + 8 := by
  have hn : ¬ n ≤ 4 := by
    intro hs
    have hh := cat_small n hs
    omega
  have hm : (n-1)%4 = 3 := by
    simp only [cat,if_neg hn] at h
    omega
  refine ⟨(n-8)/4,?_⟩
  omega

theorem category_cases (n : Nat) (h : cat n ∈ firstVariants) :
    n = 1 ∨ n = 2 ∨ n = 4 ∨
    (∃ k, n = 4*k+5) ∨ (∃ k, n = 4*k+6) ∨
    (∃ k, n = 4*k+8) := by
  simp only [firstVariants,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h
  · exact .inl (cat_one n h)
  · exact .inr (.inl (cat_two n h))
  · exact .inr (.inr (.inl (cat_four n h)))
  · exact .inr (.inr (.inr (.inl (cat_five n h))))
  · exact .inr (.inr (.inr (.inr (.inl (cat_six n h)))))
  · exact .inr (.inr (.inr (.inr (.inr (cat_eight n h)))))

#print axioms cat_one
#print axioms cat_two
#print axioms cat_four
#print axioms cat_five
#print axioms cat_six
#print axioms cat_eight
#print axioms category_cases
end BB6.Agent5Q0151RunClasses
