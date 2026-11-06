import RayTwoTierSelector
set_option maxHeartbeats 0
namespace CascadeRayTwoTierNoTwo
open CascadeResetInverse CascadeSweep CascadeOddRay CascadeFiveForced
open CascadeRayTwoTierSelector

/-- Every t=2 source odd inverse arm of a high-margin ray target
    falls in the universal odd-band dyadic gap (2^n, 3*2^(n-1)). -/
theorem ray_no_ttwo (n j k d:Nat) (hn:20≤n)
  (hm:2048*deficit n j+16384*n+16384≤2^n)
  (hz:2*ray n j+5=27*d)
  (hb:6*2^k+1≤4*d ∧ 4*d≤8*2^k-1):False:=by
  have hr:ray n j+deficit n j=4*2^n:=by
    dsimp[ray];omega
  have hlo:2^n<4*d:=by omega
  have hhi:2*(4*d)+2<3*2^n:=by omega
  exact (CascadeForkOddDead27.gap_avoids_odd_images n (4*d) hlo hhi k hb)

/-- Entire exact rooted odd-parent grammar, with t=0 and t=2
    eliminated and both low-valuation t=1 depth gates closed. -/
theorem exact_odd_fork_tthree_or_exceptional (n j:Nat) (hn:20≤n)
  (hsector:n%6=4 ∨ n%6=5)
  (hm:2048*deficit n j+16384*n+16384≤2^n):
  oddRootAt n j ↔
    ∃(q k t d:Nat), ReachC (2,0) (q,0) ∧
      (d%2=1 ∧
        (6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1) ∧
        2*ray n j+5=3^(t+1)*d ∧
        2*(2^t*d)=8*2^k+q+k+5) ∧
      (3≤t ∨ (t=1 ∧
        ((2*q+5)%27=0 ∨
         (2*(2*q-(2*2^n+(n-2)))+5)%27=0))) :=by
  constructor
  · intro hr
    obtain ⟨q,k,t,d,hroot,⟨hd,hb,hz,heq⟩,ht⟩:=
      (exact_odd_fork_two_tier_gate n j hn hsector hm).mp hr
    refine ⟨q,k,t,d,hroot,⟨hd,hb,hz,heq⟩,?_⟩
    rcases ht with ht|ht
    · by_cases htwo:t=2
      · subst t
        have hz27:2*ray n j+5=27*d:=by simpa using hz
        have hb4:6*2^k+1≤4*d ∧ 4*d≤8*2^k-1:=by simpa using hb
        exact False.elim (ray_no_ttwo n j k d hn hm hz27 hb4)
      · exact Or.inl (by omega)
    · exact Or.inr ht
  · rintro ⟨q,k,t,d,hroot,⟨hd,hband,hz,heq⟩,hgate⟩
    have htwo:2≤t ∨ (t=1 ∧
      ((2*q+5)%27=0 ∨
       (2*(2*q-(2*2^n+(n-2)))+5)%27=0)):=by
      rcases hgate with ht|ht
      · exact Or.inl (by omega)
      · exact Or.inr ht
    exact (exact_odd_fork_two_tier_gate n j hn hsector hm).mpr
      ⟨q,k,t,d,hroot,⟨hd,hband,hz,heq⟩,htwo⟩

#print axioms ray_no_ttwo
#print axioms exact_odd_fork_tthree_or_exceptional
end CascadeRayTwoTierNoTwo
