import RayTThreeGap
set_option maxHeartbeats 0
namespace CascadeRayTThreeSelector
open CascadeResetInverse CascadeSweep CascadeOddRay CascadeFiveForced
open CascadeRayTThreeGap CascadeRayTwoTierNoTwo

/-- Lossless source-exact high-margin rooted odd ray-fork classification.
    All t=0,2 branches are impossible; t=1 survives only at a
    strict high-valuation double gate; t=3 survives only at residue 2;
    t>=4 is retained without unjustified pruning. -/
theorem exact_odd_root_tthree_residue (n j:Nat) (hn:20≤n)
  (hsector:n%6=4 ∨ n%6=5)
  (hm:2048*deficit n j+16384*n+16384≤2^n):
  oddRootAt n j ↔
    ∃(q k t d:Nat), ReachC (2,0) (q,0) ∧
      (d%2=1 ∧
        (6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1) ∧
        2*ray n j+5=3^(t+1)*d ∧
        2*(2^t*d)=8*2^k+q+k+5) ∧
      (4≤t ∨ (t=3 ∧ q%3=2) ∨ (t=1 ∧
        ((2*q+5)%27=0 ∨
         (2*(2*q-(2*2^n+(n-2)))+5)%27=0))) :=by
  constructor
  · intro hr
    obtain ⟨q,k,t,d,hroot,⟨hd,hband,hz,heq⟩,ht⟩:=
      (exact_odd_fork_tthree_or_exceptional n j hn hsector hm).mp hr
    refine ⟨q,k,t,d,hroot,⟨hd,hband,hz,heq⟩,?_⟩
    rcases ht with ht|ht
    · by_cases hthree:t=3
      · subst t
        right;left
        refine ⟨rfl,?_⟩
        by_cases hres:q%3=2
        · exact hres
        · have hz81:2*ray n j+5=81*d:=by simpa using hz
          have hband8:6*2^k+1≤8*d ∧ 8*d≤8*2^k-1:=by simpa using hband
          have heq16:16*d=8*2^k+q+k+5:=by omega
          exact False.elim ((ray_tthree_parent_dead n j k d q hn hm
            hz81 hband8 heq16 hres) hroot)
      · exact Or.inl (by omega)
    · exact Or.inr (Or.inr ht)
  · rintro ⟨q,k,t,d,hroot,⟨hd,hband,hz,heq⟩,hgate⟩
    have ht:3≤t ∨ (t=1 ∧
      ((2*q+5)%27=0 ∨
       (2*(2*q-(2*2^n+(n-2)))+5)%27=0)):=by
      rcases hgate with ht|ht|ht
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · exact Or.inr ht
    exact (exact_odd_fork_tthree_or_exceptional n j hn hsector hm).mpr
      ⟨q,k,t,d,hroot,⟨hd,hband,hz,heq⟩,ht⟩

#print axioms exact_odd_root_tthree_residue
end CascadeRayTThreeSelector
