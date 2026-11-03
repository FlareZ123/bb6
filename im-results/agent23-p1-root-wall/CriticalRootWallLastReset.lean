import RootWallNoInitialUpper
import UpperTail
import CriticalRootWallOriginal

namespace BB6.Agent23RootWall
open BB6.Agent1UpperTail BB6.Agent1Quarter BB6.Agent47P1

/-- Every occurrence of the critical affine wall in a full authentic P1
    odd ancestor cone requires some positive-depth inverse earlier in that
    cone. A pure depth-zero tail from the root cannot ever reach the wall. -/
theorem critical_wall_requires_positive_inverse
    (n b d m : Nat) (hn:14≤n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hwall : b=4*(n+m)) :
    ∃ bp dp mp t k c L,
      OddCone (14*2^n-2*n-16) 3 bp dp mp ∧
      8≤bp ∧ bp%4=0 ∧ dp%2=1 ∧
      inverseAt bp dp t=some (k,c) ∧
      2≤k ∧ c%2=1 ∧ 1≤t ∧
      (2*k-4)+12 =
        2^L*(4*(n+mp+t+1+L)+12) := by
  obtain ⟨B,D,M,L,hstart,htail⟩ :=
    odd_cone_last_reset (14*2^n-2*n-16) 3 b d m hcone
  obtain ⟨hdy,hm⟩ :=
    upper_tail_dyadic B D M b d m L htail
  rcases hstart with ⟨hB,hD,hM⟩ |
    ⟨bp,dp,mp,t,k,c,hprev,hbp,hbp4,hdp,hi,hk,hc,ht,hB,hD,hM⟩
  · have hlt := exp_growth n (by omega : 4≤n)
    have hroot : (14*2^n-2*n-16)+2*n+16=14*2^n := by omega
    have hm0 : m=L := by omega
    have hbL : b=4*(n+L) := by omega
    rw [hB,hbL] at hdy
    have heq : 14*2^n=2^L*(4*(n+L)+12)+2*n+4 := by omega
    exact False.elim ((no_root_upper_wall n L hn) heq)
  · refine ⟨bp,dp,mp,t,k,c,L,hprev,hbp,hbp4,hdp,hi,hk,hc,ht,?_⟩
    have hmc : m=mp+t+1+L := by omega
    have hbL : b=4*(n+mp+t+1+L) := by omega
    rw [hB,hbL] at hdy
    exact hdy.symm

#print axioms critical_wall_requires_positive_inverse
end BB6.Agent23RootWall
