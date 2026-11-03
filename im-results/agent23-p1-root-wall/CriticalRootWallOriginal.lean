import CriticalRootWallArithmetic
import OddConeMass
import P1InverseLog
import PosEvenForm

namespace BB6.Agent23RootWall
open BB6.Agent47P1 BB6.Agent1Quarter BB6.Agent1

/-- For every critical index n >= 4, any exact odd-G inverse cone from the
    authentic critical root whose even-right feeder is genuinely blank-reachable
    has inverse cost at least 2^n, or terminates on the unique low-cost affine
    wall b=4*(n+m) at inverse depth one. This includes n=16*q+14. -/
theorem authentic_critical_root_wall_or_exponential
    (n b d m t k c : Nat) (hn : 4 ≤ n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hb : 8≤b) (hmod : b%4=0) (hd : d%2=1)
    (hinv : inverseAt b d t = some (k,c))
    (hc : 2≤c) (hceven : c%2=0) (hk : 2≤k)
    (hr : Reach (2*k-4) (c+4)) :
    2^n ≤ m ∨ (t=1 ∧ b=4*(n+m)) := by
  have hroot := odd_cone_mass _ _ b d m hcone
  have hgt : 14*n+10 < 8*2^n := exp_growth n hn
  have hrootval : b+d+2*m+2*n+13 = 14*2^n := by omega
  have hpower := inverseAt_power b d t k c hinv
  have hmass := inverseAt_exact_mass b d t k c (by omega) hmod hd hinv
  have hlin : 2*k+c+2*t+1=b+d := by omega
  obtain ⟨j,hj⟩ := even_left_power_shape (2*k-4) (c+4) hr
    (by omega) (by omega) (by omega)
  have hjval : 2*k+8 = 14*2^j := by omega
  have hmain := critical_root_even_exit_wall_or_exponential
    n b d m t k c j hn hrootval hmod hpower hceven hc hlin hjval
  rcases hmain with hcost | ⟨ht,_,hwall⟩
  · exact Or.inl hcost
  · exact Or.inr ⟨ht,hwall⟩

#print axioms authentic_critical_root_wall_or_exponential
end BB6.Agent23RootWall
