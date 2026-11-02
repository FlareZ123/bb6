import RankBridge

namespace BB6.Agent7EightThree
open BB6.P1Reduction

/-- The exceptional z=2 would require the impossible short blank hub (2,15),
    or the forbidden even-positive hub (8,8). -/
theorem no_sixteen_three : ¬BB6.Agent1.Reach 16 3 := by
  intro hr
  obtain ⟨k,v,hanc,hv,hreach⟩ :=
    BB6.Agent50P1.positive_G_feeder 16 3 (by decide) (by decide)
      (by decide) (exceptional_not_one 2 (by decide)) hr
  obtain ⟨t,ht,hmass⟩ :=
    (BB6.Agent1Quarter.ancestor_iff_power_mass 16 3 k v
      (by decide) (by decide) (by decide)).mp hanc
  have hp : 14=2^t*(v+3) := by omega
  have hdepth := depth_le_one 2 v t hp
  cases t with
  | zero =>
    have hvval : v=11 := by simpa using hp.symm
    have hpre : 2*k-4=2 := by omega
    rw [hpre,hvval] at hreach
    exact no_two_fifteen hreach
  | succ t =>
    have htzero : t=0 := by omega
    subst t
    have hvval : v=4 := by
      have hh : 14=2*(v+3) := by simpa using hp
      omega
    have hpre : 2*k-4=8 := by omega
    rw [hpre] at hreach
    obtain ⟨j,hj⟩ := BB6.Agent1.even_left_power_shape 8 (v+4)
      hreach (by decide) (by omega) (by omega)
    omega

/-- Fully exceptional-free all-time sparse power-of-four barrier.
    Applies to every positive integer z, including the sole small exception
    remaining in the previous source theorem. -/
theorem reachable_eightk_three_only_powers (z : Nat) (hz : 1≤z)
    (hr : BB6.Agent1.Reach (8*z) 3) :
    ∃ m : Nat, 3*z+4=7*4^m := by
  rcases reachable_eightk_three_power_four z hz hr with heq | h
  · subst z
    exact False.elim (no_sixteen_three (by simpa using hr))
  · exact h

#print axioms no_sixteen_three
#print axioms reachable_eightk_three_only_powers
end BB6.Agent7EightThree
