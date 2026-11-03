import RootWallArithmetic

namespace BB6.Agent1RootWall
open BB6.Agent1Quarter
open BB6.Agent1UpperTail
open BB6.Agent47P1
open BB6.Agent45TwoRoot

/-- For either genuine P1 critical feeder, any affine-wall member of its
    complete exact odd inverse cone has a positive-depth inverse ancestor.
    The final run of depth-zero inverse edges satisfies the displayed
    finite-dimensional dyadic equation. This imposes no budget bound. -/
theorem wall_requires_positive_reset
    (q b d m : Nat) (root : Bool) (hq : 1≤q)
    (hcone : OddCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m)
    (hwall : b=4*m+64*q+(if root then 12 else 16)) :
    ∃ bp dp mp t k c n,
      OddCone
        (if root then 4*u2 q-4 else 6*u2 q-2)
        (if root then 4*u2 q+9 else 2*u2 q+5)
        bp dp mp ∧
      8≤bp ∧ bp%4=0 ∧ dp%2=1 ∧
      inverseAt bp dp t=some (k,c) ∧
      2≤k ∧ c%2=1 ∧ 1≤t ∧
      (2*k-4)+12 =
        2^n*(4*(mp+t+1)+4*n+64*q+
          (if root then 12 else 16)+12) := by
  obtain ⟨B,D,M,n,hstart,heq⟩ :=
    odd_cone_wall_last_reset
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5)
      b d m q (if root then 12 else 16) hcone hwall
  rcases hstart with ⟨hB,hD,hM⟩ |
    ⟨bp,dp,mp,t,k,c,hprev,hbp,hbp4,hdp,hi,hk,hc,ht,hB,hD,hM⟩
  · exact False.elim ((no_initial_upper_wall q n root hq)
      (by simpa [hB,hM] using heq))
  · exact ⟨bp,dp,mp,t,k,c,n,
      hprev,hbp,hbp4,hdp,hi,hk,hc,ht,
      by simpa [hB,hM] using heq⟩

#print axioms wall_requires_positive_reset
end BB6.Agent1RootWall
