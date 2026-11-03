import RootWallSharpOriginal
import RootWallSharpGaps
import ShiftOdd
import EvenSeed
import ResetGate

namespace BB6.Agent23RootWall
open BB6.Agent47P1 BB6.Agent1Quarter BB6.Agent1

/-- Sharp-budget-or-single-residue necessary condition for an actual
    blank-reachable even-right feeder of any P1 critical inverse cone.
    This covers all n>=14 including the unresolved 14 mod 16 sector. -/
theorem authentic_critical_root_sharp_mod4
    (n b d m t k c : Nat) (hn : 14 ≤ n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hb : 8≤b) (hmod : b%4=0) (hd : d%2=1)
    (hinv : inverseAt b d t = some (k,c))
    (hc : 2≤c) (hceven : c%2=0) (hk : 2≤k)
    (hr : Reach (2*k-4) (c+4)) :
    14*2^n ≤ 6*m+14*n+10 ∨
    (t=1 ∧ b=4*(n+m) ∧ (m+2*n)%4=3) := by
  have hbase:=authentic_critical_root_sharp_budget
    n b d m t k c (by omega) hcone hb hmod hd hinv hc hceven hk hr
  by_cases hlarge:14*2^n≤6*m+14*n+10
  · exact Or.inl hlarge
  right
  have hbudget:6*m+14*n+10<14*2^n:=by omega
  obtain ⟨ht,hwall⟩:t=1 ∧ b=4*(n+m):=by
    rcases hbase with hl | hw
    · omega
    · exact hw
  obtain ⟨j,r,hreset,hpowseed,hseedmass⟩ := even_hub_reset_seed
    (2*k-4) (c+4) hr (by omega) (by omega) (by omega)
  have hrootmass:=odd_cone_mass _ _ b d m hcone
  have hgrowth:=exp_growth n (by omega)
  have hroot:b+d+2*m+2*n+13=14*2^n:=by omega
  have hpower:=inverseAt_power b d t k c hinv
  have hmass:=inverseAt_exact_mass b d t k c (by omega) hmod hd hinv
  have hlinear:2*k+c+2*t+1=b+d:=by omega
  have hpow:2*k+8=14*2^j:=by omega
  have harith:=critical_root_even_exit_sharp_budget
    n b d m t k c j (by omega) hroot hmod hpower hceven hc hlinear hpow
  have hjindex:j+1=n:=by
    rcases harith with hl | ⟨_,hj,_⟩
    · omega
    · exact hj
  have hbalance:r+4*n+2*m+16=14*2^n:=by omega
  have hpow8:(2^n)%8=0:=by
    have hdvd:8 ∣ (2:Nat)^n:=by
      simpa using (Nat.pow_dvd_pow 2 (show 3≤n by omega))
    exact Nat.mod_eq_zero_of_dvd hdvd
  have hmodleft:(m+2*n)%4=3:=by
    by_cases hmeven:m%2=0
    · have hrmod4:r%4=0:=by omega
      have hr12:12≤r:=by omega
      obtain ⟨z,hresetpow⟩:=reset_four_power r hreset hr12 hrmod4
      exact False.elim
        (sharp_no_low_wall_reset_power n m r z hn hbudget hbalance hresetpow)
    · have hmodd:m%2=1:=by omega
      by_cases hbad:(m+2*n)%4=1
      · have hrmod4:r%4=2:=by omega
        have hr10:10≤r:=by omega
        have hreach3:Reach (r-6) 3:=
          reset_mod_four_two_implies_three r hr10 hrmod4 hreset
        have hmod8:(r-6)%8=0:=by omega
        let u:=(r-6)/8
        have hru:r-6=8*u:=by dsimp [u]; omega
        have hu:3≤u:=by dsimp [u]; omega
        have hreach:Reach (8*u) 3:=by simpa [hru] using hreach3
        obtain ⟨z,h14⟩:=reachable_eight_three_requires_power u hu hreach
        have hbalance8:8*u+4*n+2*m+22=14*2^n:=by omega
        exact False.elim
          (sharp_no_low_wall_eight_three_power n m u z hn hbudget hbalance8 h14)
      · omega
  exact ⟨ht,hwall,hmodleft⟩

#print axioms authentic_critical_root_sharp_mod4
end BB6.Agent23RootWall
