import OddOddVal3Orbit
import EvenEvenParentFan
import M0EvenEvenSumZero
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15U5Q0W17SourceOnly

open BB6.Agent46

/-- For an even/even section target whose coordinate sum is not 0 mod 8,
    the complete original-source parent fan collapses to the direct parent.
    The zero-left and even-a bounce branches both force the sum to be 0 mod 8. -/
private theorem even_even_nonzero_sum_mod8_forces_direct
    (a k x y : Nat)
    (hxpos : 0 < x) (hxe : x % 2 = 0)
    (hy6 : 6 ≤ y) (hye : y % 2 = 0)
    (hsum : (x+y) % 8 ≠ 0)
    (hedge : secNext (a,k) = some (x,y)) :
    a = x+y-2 ∧ k = (y-2)/2 := by
  have hfan := BB6.Agent3ParentFan.even_even_parent_fan
    a k x y hxpos hxe hy6 hye hedge
  rcases hfan with hdirect | hzero | hbounce
  · exact hdirect
  · rcases hzero with ⟨_,_,n,hxy,_⟩
    have hdiv : 8 ∣ x+y := by
      refine ⟨2^n,?_⟩
      rw [hxy]
      ring
    have hmod := Nat.mod_eq_zero_of_dvd hdiv
    omega
  · rcases hbounce with ⟨ha2,haeven,_,_,n,hn,hxy,_⟩
    have hpow4 : 4 ∣ 2^(n+1) := by
      have hp := Nat.pow_dvd_pow 2 (show 2 ≤ n+1 by omega)
      simpa only [show (2:Nat)^2=4 by decide] using hp
    have htwo : 2 ∣ a+2 := by
      refine ⟨(a+2)/2,?_⟩
      omega
    rcases hpow4 with ⟨p,hp⟩
    rcases htwo with ⟨q,hq⟩
    have hdiv : 8 ∣ x+y := by
      refine ⟨p*q,?_⟩
      calc
        x+y = 2^(n+1)*(a+2) := hxy
        _ = (4*p)*(2*q) := by rw [hp,hq]
        _ = 8*(p*q) := by ring
    have hmod := Nat.mod_eq_zero_of_dvd hdiv
    omega

/-- Off-residual superset lemma only: for odd z, the q=0 target X_t is
    blank-unreachable. The authentic w=1 residual also imposes
    t=39+64*h and t=39+168*z, hence z is a multiple of 8; this theorem
    therefore does not close any authentic w=1 root. Its source-parent
    chain is retained as a reusable exact inverse calculation. -/
theorem q0_w1_odd_z_off_residual_unreachable (z : Nat) (hz : z % 2 = 1) :
    ¬ BB6.Agent3.CReach
      (44*(39+168*z)-1) (42*(39+168*z)-1) := by
  let t : Nat := 39+168*z
  let x : Nat := 44*t-1
  let y : Nat := 42*t-1
  have hxodd : x%2=1 := by dsimp [x]; omega
  have hyodd : y%2=1 := by dsimp [y]; omega
  have hy5 : 5≤y := by dsimp [y,t]; omega
  have hsize : 24≤x+y := by dsimp [x,y,t]; omega
  have hval3 : (x+y)%16=8 := by dsimp [x,y,t]; omega
  intro hX
  have hP0 := (BB6.Agent3.oddodd_val3_blank_reach_iff
    x y hxodd hyodd hy5 hval3 hsize).mp hX
  have hP : BB6.Agent3.CReach (1674+7224*z) (1654+7140*z) := by
    have hpx : (x+y-4)/2=1674+7224*z := by dsimp [x,y,t]; omega
    have hpy : (x+3*y-10)/4=1654+7140*z := by dsimp [x,y,t]; omega
    simpa [BB6.Agent3.CReach,hpx,hpy] using hP0

  have hD : BB6.Agent3.CReach (3326+14364*z) (826+3570*z) := by
    obtain ⟨a,k,hprev,hstep⟩ :=
      BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
        (1674+7224*z) (1654+7140*z) (by omega) hP
    have hdirect := even_even_nonzero_sum_mod8_forces_direct
      a k (1674+7224*z) (1654+7140*z)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) hstep
    rcases hdirect with ⟨ha,hk⟩
    have hpx : (1674+7224*z)+(1654+7140*z)-2 =
        3326+14364*z := by omega
    have hpy : (1654+7140*z-2)/2=826+3570*z := by omega
    simpa only [ha,hk,hpx,hpy] using hprev

  have hE : BB6.Agent3.CReach (4150+17934*z) (412+1785*z) := by
    obtain ⟨a,k,hprev,hstep⟩ :=
      BB6.Agent11M0SumZeroVerified.cReach_parent_of_left_gt5
        (3326+14364*z) (826+3570*z) (by omega) hD
    have hdirect := even_even_nonzero_sum_mod8_forces_direct
      a k (3326+14364*z) (826+3570*z)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) hstep
    rcases hdirect with ⟨ha,hk⟩
    have hpx : (3326+14364*z)+(826+3570*z)-2 =
        4150+17934*z := by omega
    have hpy : (826+3570*z-2)/2=412+1785*z := by omega
    simpa only [ha,hk,hpx,hpy] using hprev

  exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
    (4150+17934*z) (412+1785*z)
    (by omega) (by omega) (by omega) (by omega) hE

#print axioms q0_w1_odd_z_off_residual_unreachable

end BB6.Agent15U5Q0W17SourceOnly
