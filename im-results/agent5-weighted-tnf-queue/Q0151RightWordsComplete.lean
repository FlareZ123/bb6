import Q0151RightWords

set_option maxHeartbeats 0

/-!
A real q0-151 right word cannot have an unrepresented live suffix mask.
The first q0-151 finite model enumerates tails 2,3,4 only.  We prove that
this is not an underapproximation: after any positive-mode-live suffix,
every one-run remainder is again of one of these three kinds.  The value
1 (accepts initial N but not initial P) is impossible for the two-mode
grammar, and value 0 propagates backwards through every run.  Hence
the finite cut list contains the actual next run of every live concrete
right tape, of unbounded length.
-/

namespace BB6.Agent5Q0151RightWordsComplete
open BB6.Agent5Q0151Category
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151RightCut

theorem mask_zero (g : Int) : maskAccept 0 g = false := by
  by_cases h0 : g = 0
  · simp [maskAccept,h0]
  · by_cases h1 : g = 1
    · simp [maskAccept,h0,h1]
    · simp [maskAccept,h0,h1]

theorem pre_zero (n : Nat) : pre n 0 = 0 := by
  simp [pre,mask_zero]

theorem pre_shape (n t : Nat)
    (ht : t = 0 ∨ t = 2 ∨ t = 3 ∨ t = 4) :
    pre n t = 0 ∨ pre n t = 2 ∨ pre n t = 3 := by
  have hm : n % 4 = 0 ∨ n % 4 = 1 ∨
      n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases ht with h | h | h | h <;> subst t
  all_goals rcases hm with hm | hm | hm | hm
  all_goals simp [pre,dnext,maskAccept,hm]

theorem suffixMask_shape (xs : List Nat) :
    suffixMask xs = 0 ∨ suffixMask xs = 2 ∨
    suffixMask xs = 3 ∨ suffixMask xs = 4 := by
  induction xs with
  | nil => exact Or.inr (Or.inr (Or.inr rfl))
  | cons n ns ih =>
      change pre (cat (n+1)) (suffixMask ns) = 0 ∨
        pre (cat (n+1)) (suffixMask ns) = 2 ∨
        pre (cat (n+1)) (suffixMask ns) = 3 ∨
        pre (cat (n+1)) (suffixMask ns) = 4
      rcases pre_shape (cat (n+1)) (suffixMask ns) ih with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))

theorem suffixMask_live_variants (xs : List Nat)
    (h : suffixMask xs ≠ 0) : suffixMask xs ∈ suffixVariants := by
  rcases suffixMask_shape xs with hz | h2 | h3 | h4
  · exact False.elim (h hz)
  · simp [suffixVariants,h2]
  · simp [suffixVariants,h3]
  · simp [suffixVariants,h4]

theorem pre_mod_three_zero (n t : Nat)
    (h : n % 4 = 3) : pre n t = 0 := by
  simp [pre,dnext,maskAccept,h]

theorem cat_first_of_live (n t : Nat) (hn : 0 < n)
    (h : pre (cat n) t ≠ 0) : cat n ∈ firstVariants := by
  have hmod : n % 4 ≠ 3 := by
    intro hh
    have hc : cat n % 4 = 3 := by rw [cat_mod]; exact hh
    exact h (pre_mod_three_zero (cat n) t hc)
  by_cases hs : n ≤ 4
  · have hv : n = 1 ∨ n = 2 ∨ n = 4 := by omega
    rcases hv with h1 | h2 | h4
    · subst n; decide
    · subst n; decide
    · subst n; decide
  · have hcat : cat n = 5 + (n-1) % 4 := by
      simp [cat,hs]
    have hv : (n-1) % 4 = 0 ∨
        (n-1) % 4 = 1 ∨ (n-1) % 4 = 3 := by omega
    rcases hv with h0 | h1 | h3
    · simp [firstVariants,hcat,h0]
    · simp [firstVariants,hcat,h1]
    · simp [firstVariants,hcat,h3]

theorem cut_second_live (a b : Nat) (rest : List Nat)
    (h : suffixMask (b::rest) ≠ 0) :
    (cat (a+1),rightSig (b::rest)) ∈
      cut (rightSig (a::b::rest)) := by
  have ht : suffixMask rest ≠ 0 := by
    intro hz
    apply h
    simp only [suffixMask,hz,pre_zero]
  have hc : cat (b+1) ∈ firstVariants :=
    cat_first_of_live (b+1) (suffixMask rest) (by omega)
      (by simpa only [suffixMask] using h)
  exact cut_second a b rest hc (suffixMask_live_variants rest ht)

def actualNext : List Nat → Nat × RightSummary
  | [] => (0,emptyRight)
  | n::rest => (cat (n+1),rightSig rest)

theorem cut_real_next (xs : List Nat)
    (h : rightType (rightSig xs) ≠ 0) :
    actualNext xs ∈ cut (rightSig xs) := by
  cases xs with
  | nil => exact cut_empty
  | cons a rest =>
      cases rest with
      | nil => exact cut_single a
      | cons b bs =>
          have hl : suffixMask (b::bs) ≠ 0 := by
            intro hz
            apply h
            simp [rightSig,rightType,cat_pos a,hz,pre_zero]
          exact cut_second_live a b bs hl

#print axioms suffixMask_shape
#print axioms suffixMask_live_variants
#print axioms cat_first_of_live
#print axioms cut_second_live
#print axioms cut_real_next
end BB6.Agent5Q0151RightWordsComplete
