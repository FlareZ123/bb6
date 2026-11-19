import Agent49TernaryBufferSource

namespace BB6.Agent1ComplementBufferSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent49TernaryBufferSource

private abbrev next : HighLevelState → Option HighLevelState := highLevelNext

/-- Zero-first-counter states always have a successful high-level successor.
This local spelling keeps the theorem in the same `HighLevelState` alias as
this file rather than relying on another module's private `State` alias. -/
private theorem next_zero_total_local (d : Nat) :
    ∃ aa dd, next (.D 0 d) = some (.D aa dd) := by
  simp only [next, highLevelNext]
  by_cases hodd : d % 2 = 1
  · simp only [if_pos hodd]
    by_cases h1 : d = 1
    · subst d
      exact ⟨0, 14, by decide +kernel⟩
    · have hd : 3 ≤ d := by omega
      have hg : 2 < d + 1 := by omega
      obtain ⟨aa, dd, hr, _⟩ := drainB_safe_gap 2 (d + 1) 2 hg
      exact ⟨aa, dd, hr⟩
  · simp only [if_neg hodd]
    exact ⟨d, 7, rfl⟩

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

/-- The two odd-d near-right offsets a=d+1 and a=d+3 have a
    strong-right successor whenever their source drain succeeds. -/
theorem odd_near_diagonal_to_safe_right
    (d r b e : Nat)
    (hd : d % 2 = 1)
    (hr : r = 1 ∨ r = 3)
    (hnext : next (.D (d + r) d) = some (.D b e)) :
    b % 2 = 0 ∧ 2 * b + 1 ≤ e := by
  have h0 : d + r ≠ 0 := by omega
  have h1 : ¬(d % 2 = 1 ∧ d + r ≥ d + 5) := by
    rcases hr with h | h <;> omega
  have h2 : ¬(d % 2 = 0 ∧ d + r ≥ d + 3) := by omega
  have h3 : (d + r) % 2 ≠ 1 := by omega
  have h4 : d + r ≠ d + 2 := by
    rcases hr with h | h <;> omega
  have hstep : drainB (4 - r) (d + r - 1) 3 = some (.D b e) := by
    simp only [next, highLevelNext, if_neg h0, if_neg h1, if_neg h2,
      if_neg h3, if_neg h4, if_pos hd] at hnext
    have hsub : d + 4 - (d + r) = 4 - r := by omega
    rw [hsub] at hnext
    exact hnext
  have hfirst := drainB_first3 (d + r - 1) (4 - r) 3 b e hstep
  have hmass := drainB_mass (d + r - 1) (4 - r) 3 b e hstep
  have hparity := drainB_parity (d + r - 1) (4 - r) 3 b e hstep
  rcases hmass with ⟨_, hmass⟩
  have hblock : 0 < d + r - 1 := by
    rcases hr with h | h <;> omega
  have hmass' : (4 - r) + 3 + 2 * (d + r - 1) + 3 ≤ b + e :=
    hmass hblock
  have hparity' : b % 2 = 0 := by
    have hsum : ((4 - r) + (d + r - 1)) % 2 = 0 := by
      rcases hr with h | h <;> omega
    omega
  constructor
  · exact hparity'
  · rcases hr with h | h
    · subst r
      omega
    · subst r
      omega

/-- The even gap-two diagonal a=d+2 is the special zero-first-counter
    drain; every successful return from it is strong-right. -/
theorem even_gap_two_to_safe_right
    (d b e : Nat)
    (hd : d % 2 = 0)
    (hnext : next (.D (d + 2) d) = some (.D b e)) :
    b % 2 = 0 ∧ 2 * b + 1 ≤ e := by
  have h0 : d + 2 ≠ 0 := by omega
  have h1 : ¬(d % 2 = 1 ∧ d + 2 ≥ d + 5) := by omega
  have h2 : ¬(d % 2 = 0 ∧ d + 2 ≥ d + 3) := by omega
  have h3 : (d + 2) % 2 ≠ 1 := by omega
  have hstep : drainB 0 (d + 2) 2 = some (.D b e) := by
    simp only [next, highLevelNext, if_neg h0, if_neg h1, if_neg h2,
      if_neg h3, if_pos rfl] at hnext
    exact hnext
  have hfirst := drainB_first3 (d + 2) 0 2 b e hstep
  have hmass := drainB_mass (d + 2) 0 2 b e hstep
  have hparity := drainB_parity (d + 2) 0 2 b e hstep
  rcases hmass with ⟨_, hmass⟩
  have hmass' : 0 + 2 + 2 * (d + 2) + 3 ≤ b + e :=
    hmass (by omega)
  constructor <;> omega

/-- Every positive even state outside the exponential affine cone has
    a strong-right successor whenever its next source transition succeeds.
    This includes all three near-diagonal offsets: odd d with a=d+1 or
    a=d+3, and even d with a=d+2. -/
theorem complement_to_safe_right (a d b e : Nat)
    (ha : a % 2 = 0) (ha0 : 0 < a)
    (hnot : ¬ newAffineCone a d)
    (hnext : next (.D a d) = some (.D b e)) :
    b % 2 = 0 ∧ 2 * b + 1 ≤ e := by
  have hold : ¬ oldAffineCone a d := by
    intro ho
    exact hnot (oldAffine_subset_newAffine a d ho)
  by_cases hdodd : d % 2 = 1
  · by_cases hfar : d + 5 ≤ a
    · have hnotold : a ≤ 2 * d + 8 := by
        by_contra hlarge
        exact hold (Or.inl ⟨hdodd, by omega⟩)
      have hs := far_left_odd_to_safe_right
        a d b e ha hdodd hfar hnotold hnext
      omega
    · by_cases hnear : a = d + 1 ∨ a = d + 3
      · rcases hnear with hnear | hnear
        · subst a
          exact odd_near_diagonal_to_safe_right
            d 1 b e hdodd (Or.inl rfl) hnext
        · subst a
          exact odd_near_diagonal_to_safe_right
            d 3 b e hdodd (Or.inr rfl) hnext
      · have hside : a ≤ d := by omega
        have hnotold : d < 2 * a + 1 := by
          by_contra hlarge
          exact hold
            (Or.inr (Or.inr (Or.inl ⟨ha0, ha, hdodd, by omega⟩)))
        have hex : ¬ (a = 4 ∧ (d = 5 ∨ d = 7)) := by
          intro h
          rcases h with ⟨ha4, hd4⟩
          rcases hd4 with h5 | h7
          · subst a
            subst d
            have hcone : newAffineCone 4 5 := by
              unfold newAffineCone
              right; right; left
              norm_num [ternaryOnes]
            exact hnot hcone
          · subst a
            subst d
            have hcone : newAffineCone 4 7 := by
              unfold newAffineCone
              right; right; left
              norm_num [ternaryOnes]
            exact hnot hcone
        exact right_odd_to_safe_right
          a d b e ha ha0 hdodd hside hnotold hex hnext
  · have hdeven : d % 2 = 0 := by omega
    by_cases hfar : d + 3 ≤ a
    · have hnotold : a ≤ 2 * d + 4 := by
        by_contra hlarge
        exact hold (Or.inr (Or.inl ⟨hdeven, by omega⟩))
      have hs := far_left_even_to_safe_right
        a d b e ha hdeven hfar hnotold hnext
      omega
    · by_cases hgap : a = d + 2
      · subst a
        exact even_gap_two_to_safe_right d b e hdeven hnext
      · have hside : a ≤ d := by omega
        have hnotold : d < 2 * a + 2 := by
          by_contra hlarge
          exact hold
            (Or.inr (Or.inr (Or.inr ⟨ha0, ha, hdeven, by omega⟩)))
        exact right_even_to_safe_right
          a d b e ha ha0 hdeven hside hnotold hnext

/-- Every successful transition from a positive even state outside the
    old linear cone has a successor that itself survives one more step.
    The two small exceptions D(4,5) and D(4,7) are checked exactly. -/
theorem outside_old_predecessor_has_successor
    (a d b e : Nat)
    (ha : a % 2 = 0) (ha0 : 0 < a)
    (hnotold : ¬ oldAffineCone a d)
    (hstep : next (.D a d) = some (.D b e)) :
    ∃ c f, next (.D b e) = some (.D c f) := by
  by_cases hn : newAffineCone a d
  · by_cases hx : a = 4 ∧ (d = 5 ∨ d = 7)
    · rcases hx with ⟨rfl, hd⟩
      rcases hd with h5 | h7
      · subst d
        have hval : next (.D 4 5) = some (.D 6 12) := by simp [next, highLevelNext, drainB, evalA]
        rw [hval] at hstep
        cases hstep
        exact next_safe_left_third_two 6 12 (by decide) (by decide) (by decide)
      · subst d
        have hval : next (.D 4 7) = some (.D 8 12) := by simp [next, highLevelNext, drainB, evalA]
        rw [hval] at hstep
        cases hstep
        exact next_safe_left_third_two 8 12 (by decide) (by decide) (by decide)
    · have hsafe := newAffine_to_oldRight a d b e ha hn hnotold hx hstep
      by_cases hb0 : b = 0
      subst b
      exact next_zero_total_local e
      · have hbpos : 0 < b := by omega
        have hdiv : b / 3 ≤ b := Nat.div_le_self _ _
        have hbudget : b + b / 3 + 1 ≤ e := by omega
        exact next_safe_left_third_two b e hbpos hsafe.1 hbudget
  · have hsafe := complement_to_safe_right a d b e ha ha0 hn hstep
    by_cases hb0 : b = 0
    subst b
    exact next_zero_total_local e
    · have hbpos : 0 < b := by omega
      have hdiv : b / 3 ≤ b := Nat.div_le_self _ _
      have hbudget : b + b / 3 + 1 ≤ e := by omega
      exact next_safe_left_third_two b e hbpos hsafe.1 hbudget

/-- Therefore any halting state reached in one step from a positive even
    state must have that predecessor in the old linear affine cone. -/
theorem halt_parent_in_oldAffineCone
    (a d b e : Nat)
    (ha : a % 2 = 0) (ha0 : 0 < a)
    (hstep : next (.D a d) = some (.D b e))
    (hhalt : next (.D b e) = none) :
    oldAffineCone a d := by
  by_contra hnotold
  obtain ⟨c, f, hcont⟩ :=
    outside_old_predecessor_has_successor a d b e ha ha0 hnotold hstep
  rw [hhalt] at hcont
  cases hcont

#print axioms ternaryOnes_ge_self
#print axioms oldAffine_subset_newAffine
#print axioms odd_near_diagonal_to_safe_right
#print axioms even_gap_two_to_safe_right
#print axioms complement_to_safe_right
#print axioms outside_old_predecessor_has_successor
#print axioms halt_parent_in_oldAffineCone

end BB6.Agent1ComplementBufferSource
