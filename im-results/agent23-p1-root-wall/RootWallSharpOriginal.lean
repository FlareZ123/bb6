import RootWallSharpArithmetic
import CriticalRootWallOriginal

namespace BB6.Agent23RootWall
open BB6.Agent47P1 BB6.Agent1Quarter BB6.Agent1

/-- A genuine blank-reachable even-right exit from a P1 critical-root
    odd inverse cone either meets the sharp exponential cost budget or
    belongs to the exact depth-one affine wall, for every n>=4. -/
theorem authentic_critical_root_sharp_budget
    (n b d m t k c : Nat) (hn : 4 ≤ n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hb : 8≤b) (hmod : b%4=0) (hd : d%2=1)
    (hinv : inverseAt b d t = some (k,c))
    (hc : 2≤c) (hceven : c%2=0) (hk : 2≤k)
    (hr : Reach (2*k-4) (c+4)) :
    14*2^n ≤ 6*m+14*n+10 ∨
    (t=1 ∧ b=4*(n+m)) := by
  have hrootmass := odd_cone_mass _ _ b d m hcone
  have hgrowth := exp_growth n hn
  have hroot : b+d+2*m+2*n+13=14*2^n := by omega
  have hpower := inverseAt_power b d t k c hinv
  have hmass := inverseAt_exact_mass b d t k c (by omega) hmod hd hinv
  have hlinear : 2*k+c+2*t+1=b+d := by omega
  obtain ⟨j,hj⟩ := even_left_power_shape (2*k-4) (c+4) hr
    (by omega) (by omega) (by omega)
  have hpow : 2*k+8=14*2^j := by omega
  have hmain := critical_root_even_exit_sharp_budget
    n b d m t k c j hn hroot hmod hpower hceven hc hlinear hpow
  rcases hmain with hbudget | ⟨ht,_,hwall⟩
  · exact Or.inl hbudget
  · exact Or.inr ⟨ht,hwall⟩

#print axioms authentic_critical_root_sharp_budget
end BB6.Agent23RootWall
