import FiniteSlopeTransport

namespace PeriodicMacro

theorem walk_rank_exact {xs : List Letter} {u r U R : Nat}
    (h : Walk xs u r U R) : R=r+T xs := by
  induction h with
  | nil u r => simp [T]
  | @cons x xs u r v s U R hstep tail ih =>
      rcases hstep with ⟨_,hs⟩
      simp only [T]
      omega

/-- Two consecutive copies whose first coordinates have zero second
    difference produce a closed finite slope recurrence across the word. -/
theorem affine_two_walks_give_slope_cycle
    {xs : List Letter}
    {u0 r0 u1 r1 u2 r2 : Nat}
    (h0 : Walk xs u0 r0 u1 r1)
    (h1 : Walk xs u1 r1 u2 r2)
    (hmono : u0≤u1)
    (haff : u0+u2=2*u1) :
    ∃ d : Nat, u1=u0+d ∧ u2=u1+d ∧
      SlopeWalk (T xs) xs d d := by
  let d := u1-u0
  have hd0 : u1=u0+d := by dsimp [d]; omega
  have hd1 : u2=u1+d := by dsimp [d]; omega
  have hr0 := walk_rank_exact h0
  obtain ⟨e,heU,heR,hslope⟩ :=
    parallel_walk_slope h0 h1 hd0 hr0
  have hed : e=d := by omega
  subst e
  exact ⟨d,hd0,hd1,hslope⟩

#print axioms walk_rank_exact
#print axioms affine_two_walks_give_slope_cycle
end PeriodicMacro
