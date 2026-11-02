import EightThree

/-!
An all-time two-parameter blank-reachability restriction for the source P1
accelerator at (8z,4w+3). The small exceptional left counters z=1,2 are
preserved because genuine blank-orbit states can occur there.
-/

namespace BB6.Agent7EightThree
open BB6.P1Reduction

theorem exceptional_not_one_all (z w : Nat) (hz:1≤z) :
    ∀ k, ¬GAncestor (8*z) (4*w+3) k 1 := by
  intro k h
  obtain ⟨t,ht,_⟩ :=
    (BB6.Agent1Quarter.ancestor_iff_power_mass (8*z) (4*w+3) k 1
      (by omega) (by omega) (by omega)).mp h
  have heq : 4*(z+w)+6=4*2^t := by omega
  have hdvd : 4 ∣ 4*(z+w)+6 := by
    rw [heq]
    refine ⟨2^t,?_⟩
    simp [Nat.mul_comm]
  omega

/-- Reachable multiples of eight with right counter congruent to three
modulo four satisfy a dyadic affine relation, apart from z=1,2. -/
theorem reachable_eight_fourw_three_sparse (z w : Nat) (hz : 1≤z)
    (hr : BB6.Agent1.Reach (8*z) (4*w+3)) :
    z=1 ∨ z=2 ∨ ∃ j : Nat, 3*z+w+4=7*2^j := by
  obtain ⟨k,v,hanc,hv,hreach⟩ :=
    BB6.Agent50P1.positive_G_feeder (8*z) (4*w+3)
      (by omega) (by omega) (by omega)
      (exceptional_not_one_all z w hz) hr
  obtain ⟨t,ht,hmass⟩ :=
    (BB6.Agent1Quarter.ancestor_iff_power_mass (8*z) (4*w+3) k v
      (by omega) (by omega) (by omega)).mp hanc
  have hp : 4*(z+w)+6=2^t*(v+3) := by omega
  have hdepth := depth_le_one (z+w) v t hp
  cases t with
  | zero =>
    have hvval : v=4*z+4*w+3 := by
      have hh : 4*(z+w)+6=v+3 := by simpa using hp
      omega
    have hk : 2*k=4*z-2 := by omega
    by_cases hz1 : z=1
    · exact Or.inl hz1
    · by_cases hz2 : z=2
      · exact Or.inr (Or.inl hz2)
      · have hz3 : 3≤z := by omega
        have hpre : 2*k-4=4*z-6 := by omega
        rw [hpre] at hreach
        have hinv := BB6.Agent1.reachable_even_mod4 (4*z-6) (v+4)
          hreach (by omega) (by omega)
        rcases hinv with h | h
        · omega
        · omega
  | succ t =>
    have htzero : t=0 := by omega
    subst t
    have hvval : v=2*z+2*w := by
      have hh : 4*(z+w)+6=2*(v+3) := by simpa using hp
      omega
    have hpre : 2*k-4=6*z+2*w-4 := by omega
    rw [hpre] at hreach
    obtain ⟨j,hj⟩ := BB6.Agent1.even_left_power_shape (6*z+2*w-4) (v+4)
      hreach (by omega) (by omega) (by omega)
    right
    right
    refine ⟨j,?_⟩
    omega

private theorem pow_two_mod_three_general (j : Nat) :
    2^j % 3 = if j%2=0 then 1 else 2 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    by_cases hj : j%2=0
    · have hs : (j+1)%2 ≠ 0 := by omega
      simp [ih, hj, hs]
    · have hs : (j+1)%2 = 0 := by omega
      simp [ih, hj, hs]

/-- Infinite affine exclusion of all (8z,4w+3) with z>=3 and w=2(mod3). -/
theorem no_eight_odd_three_mod_three (z w : Nat)
    (hz : 3≤z) (hw : w%3=2) :
    ¬BB6.Agent1.Reach (8*z) (4*w+3) := by
  intro hr
  rcases reachable_eight_fourw_three_sparse z w (by omega) hr with h1 | h2 | ⟨j,hj⟩
  · omega
  · omega
  · have hzero : 2^j%3=0 := by omega
    have hp := pow_two_mod_three_general j
    by_cases hpar : j%2=0
    · simp [hpar] at hp
      omega
    · simp [hpar] at hp
      omega

#print axioms reachable_eight_fourw_three_sparse
#print axioms no_eight_odd_three_mod_three
end BB6.Agent7EightThree
