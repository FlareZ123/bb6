import CriticalRootWallOddCost
import RootWallEightThreeArithmetic
import ShiftOdd

namespace BB6.Agent23RootWall
open BB6.Agent47P1 BB6.Agent1Quarter BB6.Agent1

/-- Any genuinely blank-reachable even-right exit from an authentic P1
    critical-root inverse cone has exponential cost, or is a depth-one
    affine-wall exit in a single inverse-cost residue modulo four. -/
theorem authentic_critical_root_wall_mod4
    (n b d m t k c : Nat) (hn : 4 ≤ n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hb : 8≤b) (hmod : b%4=0) (hd : d%2=1)
    (hinv : inverseAt b d t = some (k,c))
    (hc : 2≤c) (hceven : c%2=0) (hk : 2≤k)
    (hr : Reach (2*k-4) (c+4)) :
    2^n ≤ m ∨
    (t=1 ∧ b=4*(n+m) ∧ (m+2*n)%4=3) := by
  have hbase := authentic_critical_root_wall_odd_cost
    n b d m t k c hn hcone hb hmod hd hinv hc hceven hk hr
  by_cases hcost : 2^n≤m
  · exact Or.inl hcost
  right
  have hsmall : m<2^n := by omega
  obtain ⟨ht,hwall,hodd⟩ :
      t=1 ∧ b=4*(n+m) ∧ m%2=1 := by
    rcases hbase with hc | hw
    · omega
    · exact hw
  have hmodleft : (m+2*n)%4=3 := by
    by_cases hbad : (m+2*n)%4=1
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
      have hpow8 : (2^n)%8=0 := by
        have hdiv : 8 ∣ (2:Nat)^n := by
          simpa using (Nat.pow_dvd_pow 2 (show 3 ≤ n by omega))
        exact Nat.mod_eq_zero_of_dvd hdiv
      have hrmod : r%4=2 := by omega
      have hr10 : 10≤r := by omega
      have hr3 : Reach (r-6) 3 :=
        reset_mod_four_two_implies_three r hr10 hrmod hreset
      have hmod8 : (r-6)%8=0 := by omega
      let u := (r-6)/8
      have hrueq : r-6=8*u := by dsimp [u]; omega
      have hu : 3≤u := by dsimp [u]; omega
      have hreach : Reach (8*u) 3 := by simpa [hrueq] using hr3
      obtain ⟨z,hpow⟩ := reachable_eight_three_requires_power u hu hreach
      have hbalance2 : 8*u+4*n+2*m+22=14*2^n := by omega
      exact False.elim (no_low_wall_eight_three_power n m u z hn hsmall hbalance2 hpow)
    · omega
  exact ⟨ht,hwall,hmodleft⟩

#print axioms authentic_critical_root_wall_mod4
end BB6.Agent23RootWall
