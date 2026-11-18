import Agent49TernaryBufferSource

namespace BB6.Agent1ComplementBufferSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent49TernaryBufferSource

/-- Elementary lower bound used to embed the old linear cone into the
    sharp exponential cone. -/
theorem ternaryOnes_ge_self : ∀ n : Nat, n ≤ ternaryOnes n := by
  intro n
  induction n with
  | zero =>
      simp [ternaryOnes]
  | succ n ih =>
      simp only [ternaryOnes]
      omega

/-- Every old linear affine sector is contained in the newer exponential
    affine cone. -/
theorem oldAffine_subset_newAffine (a d : Nat)
    (h : oldAffineCone a d) :
    newAffineCone a d := by
  rcases h with h | h | h | h
  · rcases h with ⟨hd, hlin⟩
    left
    refine ⟨hd, ?_, ?_⟩
    · omega
    · have hres : d + 4 ≤ a - d - 5 := by omega
      have ho := ternaryOnes_ge_self (a - d - 5)
      omega
  · rcases h with ⟨hd, hlin⟩
    right
    left
    refine ⟨hd, ?_, ?_⟩
    · omega
    · have hres : d + 3 ≤ a - d - 2 := by omega
      have ho := ternaryOnes_ge_self (a - d - 2)
      omega
  · rcases h with ⟨ha0, he, hd, hlin⟩
    right
    right
    left
    refine ⟨ha0, he, ?_, hd, ?_⟩
    · omega
    · have hres : a + 5 ≤ d + 4 - a := by omega
      have ho := ternaryOnes_ge_self (d + 4 - a)
      omega
  · rcases h with ⟨ha0, he, hd, hlin⟩
    right
    right
    right
    refine ⟨ha0, he, ?_, hd, ?_⟩
    · omega
    · have hres : a + 2 ≤ d + 1 - a := by omega
      have ho := ternaryOnes_ge_self (d + 1 - a)
      omega

/-- A positive even state outside the sharp exponential cone has a
    strong-right successful successor, unless it lies on one of the two
    adjacent-diagonal boundary families a=d+3 (d odd) or a=d+2 (d even).
    Zero first-counter outputs are retained explicitly. -/
theorem complement_to_safe_right (a d b e : Nat)
    (ha : a % 2 = 0) (ha0 : 0 < a)
    (hnot : ¬ newAffineCone a d)
    (hboundary :
      ¬ ((d % 2 = 1 ∧ a = d + 3) ∨
         (d % 2 = 0 ∧ a = d + 2)))
    (hnext : next (.D a d) = some (.D b e)) :
    b = 0 ∨ (b % 2 = 0 ∧ 2*b + 1 ≤ e) := by
  have hold : ¬ oldAffineCone a d := by
    intro ho
    exact hnot (oldAffine_subset_newAffine a d ho)
  by_cases hdodd : d % 2 = 1
  · by_cases hfar : d + 5 ≤ a
    · have hnotold : a ≤ 2*d + 8 := by
        by_contra hlarge
        exact hold (Or.inl ⟨hdodd, by omega⟩)
      have hs := far_left_odd_to_safe_right
        a d b e ha hdodd hfar hnotold hnext
      omega
    · have hnot_boundary : a ≠ d + 3 := by
        intro hEq
        apply hboundary
        exact Or.inl ⟨hdodd, hEq⟩
      have hside : a ≤ d := by omega
      have hnotold : d < 2*a + 1 := by
        by_contra hlarge
        exact hold
          (Or.inr (Or.inr (Or.inl ⟨ha0, ha, hdodd, by omega⟩)))
      have hex : ¬ (a = 4 ∧ (d = 5 ∨ d = 7)) := by
        intro h
        rcases h with ⟨ha4, hd4⟩
        rcases hd4 with h5 | h7
        · subst a; subst d
          exact hnot (by decide)
        · subst a; subst d
          exact hnot (by decide)
      have hs := right_odd_to_safe_right
        a d b e ha ha0 hdodd hside hnotold hex hnext
      omega
  · have hdeven : d % 2 = 0 := by omega
    by_cases hfar : d + 3 ≤ a
    · have hnotold : a ≤ 2*d + 4 := by
        by_contra hlarge
        exact hold (Or.inr (Or.inl ⟨hdeven, by omega⟩))
      have hs := far_left_even_to_safe_right
        a d b e ha hdeven hfar hnotold hnext
      omega
    · have hside : a ≤ d := by
        by_contra hgt
        have hdiff : a = d + 2 := by omega
        apply hboundary
        exact Or.inr ⟨hdeven, hdiff⟩
      have hnotold : d < 2*a + 2 := by
        by_contra hlarge
        exact hold
          (Or.inr (Or.inr (Or.inr ⟨ha0, ha, hdeven, by omega⟩)))
      have hs := right_even_to_safe_right
        a d b e ha ha0 hdeven hside hnotold hnext
      omega

#print axioms ternaryOnes_ge_self
#print axioms oldAffine_subset_newAffine
#print axioms complement_to_safe_right

end BB6.Agent1ComplementBufferSource
