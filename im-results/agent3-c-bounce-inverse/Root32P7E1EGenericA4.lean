import Root32HighStopA4Core
import Root32HighStopIntegrated
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

namespace BB6.Agent3Root32P7E1EGenericA4

open BB6.Agent3Root32HighStopIntegrated
open BB6.Agent3Root32HighStopA4Core

abbrev RunReach (x y : Nat) : Prop :=
  BB6.Agent3Root32HighStopIntegrated.RunReach x y

/-- On every t≡7 (mod 8) slice of the existing root32 index map,
    the corrected P7E1E residual has a forced direct parent D(t),
    and D(t)'s unique odd-seven predecessor is A4(t). This isolates
    the common odd/odd high-valuation residual for all eight t≡3
    (mod 4) cylinders without assuming the t≡31 (mod32) low-value
    condition. -/
theorem p7e1e_reach_implies_a4_t7 (t : Nat) (ht8 : t%8=7)
    (hreach : RunReach (p7e1eX t) (p7e1eY t)) :
    RunReach (a4X t) (a4Y t) := by
  have hsumMod : (p7e1eX t+p7e1eY t)%8=2 := by
    dsimp [p7e1eX,p7e1eY]
    omega
  have hx : 5<p7e1eX t := by
    dsimp [p7e1eX]
    omega
  have hxe : p7e1eX t%2=0 := by
    dsimp [p7e1eX]
    omega
  have hy6 : 6≤p7e1eY t := by
    dsimp [p7e1eY]
    omega
  have hye : p7e1eY t%2=0 := by
    dsimp [p7e1eY]
    omega
  have hreachA4 : BB6.Agent3Root32HighStopA4Core.RunReach
      (p7e1eX t) (p7e1eY t) := by
    simpa [RunReach,BB6.Agent3Root32HighStopIntegrated.RunReach,
      BB6.Agent3Root32HighStopA4Core.RunReach] using hreach
  obtain ⟨a,k,hprev,hstep⟩ :=
    BB6.Agent3Root32HighStopA4Core.run_parent_of_left_gt5
      (p7e1eX t) (p7e1eY t) hx hreachA4
  have hfan := BB6.Agent3ParentFan.even_even_parent_fan
    a k (p7e1eX t) (p7e1eY t)
    (by omega) hxe hy6 hye hstep
  rcases hfan with hdirect | hzero | hbounce
  · rcases hdirect with ⟨ha,hk⟩
    have hDx : p7e1eX t+p7e1eY t-2=p7e1eDX t := by
      dsimp [p7e1eX,p7e1eY,p7e1eDX]
      omega
    have hDy : (p7e1eY t-2)/2=p7e1eDY t := by
      dsimp [p7e1eY,p7e1eDY]
      omega
    have hDreachA4 :
        BB6.Agent3Root32HighStopA4Core.RunReach
          (p7e1eDX t) (p7e1eDY t) := by
      simpa only [ha,hk,hDx,hDy] using hprev
    have hDreach : RunReach (p7e1eDX t) (p7e1eDY t) := by
      simpa [RunReach,BB6.Agent3Root32HighStopA4Core.RunReach] using hDreachA4
    have hDxEven : p7e1eDX t%2=0 := by
      dsimp [p7e1eDX]
      omega
    have hDyOdd : p7e1eDY t%2=1 := by
      dsimp [p7e1eDY]
      omega
    have hDy5 : 5≤p7e1eDY t := by
      dsimp [p7e1eDY]
      omega
    have hDmod : (p7e1eDX t+p7e1eDY t+1)%16=8 := by
      dsimp [p7e1eDX,p7e1eDY]
      omega
    have hDsize : 23≤p7e1eDX t+p7e1eDY t := by
      dsimp [p7e1eDX,p7e1eDY]
      omega
    have hDreachC : BB6.Agent3.CReach (p7e1eDX t) (p7e1eDY t) := by
      simpa [RunReach,BB6.Agent3Root32HighStopIntegrated.RunReach,
        BB6.Agent3.CReach] using hDreach
    have hiff := (BB6.Agent3.odd_seven_blank_reach_iff
      (p7e1eDX t) (p7e1eDY t)
      hDxEven hDyOdd hDy5 hDmod hDsize).mp hDreachC
    have hAx : (p7e1eDX t+p7e1eDY t-5)/2=a4X t := by
      dsimp [p7e1eDX,p7e1eDY,a4X]
      omega
    have hAy : (p7e1eDX t+3*p7e1eDY t-9)/4=a4Y t := by
      dsimp [p7e1eDX,p7e1eDY,a4Y]
      omega
    have hA4 : RunReach (a4X t) (a4Y t) := by
      simpa [RunReach,BB6.Agent3Root32HighStopIntegrated.RunReach,
        BB6.Agent3.CReach,hAx,hAy] using hiff
    exact hA4
  · rcases hzero with ⟨_,_,n,hsum,_⟩
    have hmod : (p7e1eX t+p7e1eY t)%8=0 := by
      rw [hsum]
      simp [Nat.mul_mod]
    omega
  · rcases hbounce with ⟨_,haeven,_,_,n,hnodd,hsum,_⟩
    have hpow : 4∣2^(n+1) := by
      change 2^2∣2^(n+1)
      exact Nat.pow_dvd_pow 2 (by omega)
    have ha2 : 2∣a+2 := by
      refine ⟨(a+2)/2,?_⟩
      omega
    obtain ⟨u,hu⟩ := hpow
    obtain ⟨v,hv⟩ := ha2
    have hdiv : 8∣p7e1eX t+p7e1eY t := by
      refine ⟨u*v,?_⟩
      calc
        p7e1eX t+p7e1eY t=2^(n+1)*(a+2) := hsum
        _=(4*u)*(2*v) := by rw [hu,hv]
        _=8*(u*v) := by ac_rfl
    have hmod : (p7e1eX t+p7e1eY t)%8=0 :=
      Nat.mod_eq_zero_of_dvd hdiv
    omega

#print axioms p7e1e_reach_implies_a4_t7

end BB6.Agent3Root32P7E1EGenericA4
