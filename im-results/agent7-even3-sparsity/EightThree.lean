import InverseIff
import P1ResidualReach

/-!
A blank-reachability necessary condition for (8z,3) hubs of the
exact P1 accelerator. The imported inverse relation and reachability
theorems are compiled from the original repository sources.
This does not decide the six-state machine.
-/

namespace BB6.Agent7EightThree
open BB6.P1Reduction

private theorem pow_two_mul_four (t v : Nat) :
    4 ∣ 2^(t+2)*(v+3) := by
  refine ⟨2^t*(v+3),?_⟩
  simp [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private theorem depth_le_one (z v t : Nat)
    (h : 4*z+6=2^t*(v+3)) : t≤1 := by
  by_cases hle : t≤1
  · exact hle
  · have he : t = (t-2)+2 := by omega
    rw [he] at h
    have hfour : 4 ∣ 4*z+6 := by
      rw [h]
      exact pow_two_mul_four (t-2) v
    omega

private theorem exceptional_not_one (z : Nat) (hz : 1≤z) :
    ∀ k, ¬GAncestor (8*z) 3 k 1 := by
  intro k h
  obtain ⟨t,ht,_⟩ :=
    (BB6.Agent1Quarter.ancestor_iff_power_mass (8*z) 3 k 1
      (by omega) (by omega) (by decide)).mp h
  have heq : 4*z+6=2^t*4 := by omega
  have hdvd : 4∣4*z+6 := by
    rw [heq]
    refine ⟨2^t,?_⟩
    simp [Nat.mul_comm]
  omega

/-- Every blank-reachable even-left multiple-of-eight and right counter 3
satisfies a sparse power-of-four obstruction, apart from z=2. -/
theorem reachable_eightk_three_sparse (z : Nat) (hz : 1≤z)
    (hr : BB6.Agent1.Reach (8*z) 3) :
    z=2 ∨ ∃ j : Nat, 3*z+4=7*2^j := by
  obtain ⟨k,v,hanc,hv,hreach⟩ :=
    BB6.Agent50P1.positive_G_feeder (8*z) 3 (by omega) (by omega)
      (by decide) (exceptional_not_one z hz) hr
  obtain ⟨t,ht,hmass⟩ :=
    (BB6.Agent1Quarter.ancestor_iff_power_mass (8*z) 3 k v
      (by omega) (by omega) (by decide)).mp hanc
  have hp : 4*z+6=2^t*(v+3) := by omega
  have hdepth := depth_le_one z v t hp
  cases t with
  | zero =>
    have hvval : v=4*z+3 := by simpa using hp.symm
    have hvodd : v%2=1 := by omega
    have hk : 2*k=4*z-2 := by omega
    by_cases hz1 : z=1
    · right
      refine ⟨0,?_⟩
      simp [hz1]
    · by_cases hz2 : z=2
      · exact Or.inl hz2
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
    have hvval : v=2*z := by
      have hh : 4*z+6=2*(v+3) := by simpa using hp
      omega
    have hveven : v%2=0 := by omega
    have hkv : 2*k=6*z := by omega
    have hpre : 2*k-4=6*z-4 := by omega
    rw [hpre] at hreach
    have hpower := BB6.Agent1.even_left_power_shape (6*z-4) (v+4)
      hreach (by omega) (by omega) (by omega)
    obtain ⟨j,hj⟩ := hpower
    right
    refine ⟨j,?_⟩
    omega

#print axioms reachable_eightk_three_sparse
end BB6.Agent7EightThree
