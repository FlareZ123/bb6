import RootWallOddCostArithmetic
import CriticalRootWallOriginal
import EvenSeed
import ResetGate

namespace BB6.Agent23RootWall
open BB6.Agent47P1 BB6.Agent1Quarter BB6.Agent1

/-- A genuine P1 even feeder from any critical-root odd inverse cone either
    costs at least 2^n or has odd-cost, depth-one and a unique affine left
    coordinate. Covers every n>=4, including n%16=14. -/
theorem authentic_critical_root_wall_odd_cost
    (n b d m t k c : Nat) (hn : 4 ≤ n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hb : 8≤b) (hmod : b%4=0) (hd : d%2=1)
    (hinv : inverseAt b d t = some (k,c))
    (hc : 2≤c) (hceven : c%2=0) (hk : 2≤k)
    (hr : Reach (2*k-4) (c+4)) :
    2^n ≤ m ∨ (t=1 ∧ b=4*(n+m) ∧ m%2=1) := by
  have hbase := authentic_critical_root_wall_or_exponential
    n b d m t k c hn hcone hb hmod hd hinv hc hceven hk hr
  by_cases hcost : 2^n≤m
  · exact Or.inl hcost
  right
  have hsmall : m<2^n := by omega
  obtain ⟨ht,hwall⟩ : t=1 ∧ b=4*(n+m) := by
    rcases hbase with hc | hw
    · omega
    · exact hw
  have hodd : m%2=1 := by
    by_cases heven : m%2=0
    · obtain ⟨j, r, hreset, hevenpow, hseedmass⟩ := even_hub_reset_seed
        (2*k-4) (c+4) hr (by omega) (by omega) (by omega)
      have hrootmass := odd_cone_mass _ _ b d m hcone
      have hgrowth := exp_growth n hn
      have hroot : b+d+2*m+2*n+13=14*2^n := by omega
      have hpower := inverseAt_power b d t k c hinv
      have hmass := inverseAt_exact_mass b d t k c (by omega) hmod hd hinv
      have hlinear : 2*k+c+2*t+1=b+d := by omega
      have hevenpow' : 2*k+8=14*2^j := by omega
      have hmath := critical_root_even_exit_wall_or_exponential
        n b d m t k c j hn hroot hmod hpower hceven hc hlinear hevenpow'
      have hjindex : j+1=n := by
        rcases hmath with hl | ⟨_, hj, _⟩
        · omega
        · exact hj
      have hbalance : r+4*n+2*m+16=14*2^n := by omega
      have hpow4 : (2^n)%4=0 := by
        have hdiv : 4 ∣ (2:Nat)^n := by
          simpa using (Nat.pow_dvd_pow 2 (show 2 ≤ n by omega))
        exact Nat.mod_eq_zero_of_dvd hdiv
      have hrmod : r%4=0 := by omega
      have hr12 : 12≤r := by omega
      obtain ⟨z,hresetpow⟩ := reset_four_power r hreset hr12 hrmod
      exact False.elim (no_low_wall_reset_power n m r z hn hsmall hbalance hresetpow)
    · omega
  exact ⟨ht,hwall,hodd⟩

#print axioms authentic_critical_root_wall_odd_cost
end BB6.Agent23RootWall
