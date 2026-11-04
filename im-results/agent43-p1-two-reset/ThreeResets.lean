import SourceTwoReset

namespace BB6.Agent43
open BB6.Agent28 BB6.Agent1Quarter BB6.Agent1UpperTail BB6.Agent47P1

/-- Original-source critical P1 affine-wall histories cannot contain zero,
    one, or two positive-depth inverses, for any exponent n≥70. -/
theorem source_critical_wall_every_count_at_least_three
    (n b d m z : Nat) (hn : 70≤n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hwall : b=4*(m+n))
    (hcount : CountCone (14*2^n-2*n-16) 3 b d m z) :
    3≤z := by
  by_cases hlarge : 3≤z
  · exact hlarge
  have hcases : z=0 ∨ z=1 ∨ z=2 := by omega
  rcases hcases with hzero | hone | htwo
  · obtain ⟨r,htail⟩ :=
      (cone_shape _ _ b d m z hcount).1 hzero
    exact False.elim
      (source_critical_zero_reset_no_wall n b d m r (by omega) htail hwall)
  · obtain ⟨bp,dp,mp,r,t,k,c,s,
        hpre,hbp,hbp4,hdp,hi,hk,hc,ht,hpost⟩ :=
      (cone_shape _ _ b d m z hcount).2 hone
    exact False.elim
      (source_critical_one_reset_no_wall n bp dp mp r t k c b d m s
        (by omega) ht hpre hbp hbp4 hdp hi hk hc hpost hcone hwall)
  · have hcount2 : CountCone (14*2^n-2*n-16) 3 b d m 2 := by
      simpa only [htwo] using hcount
    exact False.elim
      (source_critical_exact_two_reset_no_wall n b d m hn hcone hcount2 hwall)

/-- Original-source affine wall requires at least three genuine resets,
    with an exact CountCone witness extracted from the original OddCone. -/
theorem source_critical_wall_needs_three_resets
    (n b d m : Nat) (hn : 70≤n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hwall : b=4*(m+n)) :
    ∃ z, CountCone (14*2^n-2*n-16) 3 b d m z ∧ 3≤z := by
  obtain ⟨z,hcount⟩ := odd_cone_has_count _ _ b d m hcone
  exact ⟨z,hcount,
    source_critical_wall_every_count_at_least_three n b d m z hn hcone hwall hcount⟩

#print axioms BB6.Agent43.source_critical_wall_every_count_at_least_three
#print axioms BB6.Agent43.source_critical_wall_needs_three_resets
end BB6.Agent43
