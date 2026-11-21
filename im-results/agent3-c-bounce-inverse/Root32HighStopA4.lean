import Root32HighStopP7
import OddSevenOrbit
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

namespace BB6.Agent3Root32HighStopA4

open BB6.Agent46
open BB6.Agent3Root32HighStopIntegrated
open BB6.Agent3Root32HighStopS1

/-- The corrected P7E1E residual's left coordinate. -/
def a4X (t : Nat) : Nat := 2814461475*t + 754739388

/-- The corrected P7E1E residual's right coordinate. -/
def a4Y (t : Nat) : Nat := (4231969245*t + 1134865019)/2

/-- The corrected P7E1E residual itself. -/
def p7e1eX (t : Nat) : Nat := 1376399640*t + 369101882
def p7e1eY (t : Nat) : Nat := 2835015540*t + 760251268

/-- Its forced direct parent. -/
def p7e1eDX (t : Nat) : Nat := 4211415180*t + 1129353148
def p7e1eDY (t : Nat) : Nat := 1417507770*t + 380125633

/-- On t = 31 (mod 32), A4 lies in the exact odd/odd valuation-three
    layer. These are the hypotheses for the source-certified low-value
    odd/odd inverse. -/
theorem a4_t31_facts (t : Nat) (ht : t%32=31) :
    5 < a4X t ∧
    5 ≤ a4Y t ∧
    a4X t%2=1 ∧
    a4Y t%2=1 ∧
    (a4X t+a4Y t)%4=0 ∧
    (a4X t+a4Y t)%16=8 ∧
    24 ≤ a4X t+a4Y t := by
  have htmin : 31≤t := by omega
  have ht4 : t%4=3 := by omega
  have hy2 : 2*a4Y t = 4231969245*t+1134865019 := by
    dsimp [a4Y]
    omega
  have hsum2 : 2*(a4X t+a4Y t) =
      9860892195*t+2644343795 := by
    dsimp [a4X,a4Y]
    omega
  have hN : (9860892195*t+2644343795)%32=16 := by omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [a4X]
    omega
  · dsimp [a4Y]
    omega
  · dsimp [a4X]
    omega
  · omega
  · omega
  · omega
  · dsimp [a4X]
    omega

/-- The A4 target is genuinely blank-unreachable throughout
    t = 31 (mod 32). Its unique low-valuation odd/odd source parent has
    odd right coordinate and sum 1 (mod 4), contradicting the global
    blank odd-image theorem. -/
theorem a4_unreachable_of_t_mod32_31 (t : Nat) (ht : t%32=31) :
    ¬ RunReach (a4X t) (a4Y t) := by
  intro hreach
  rcases a4_t31_facts t ht with
    ⟨hx,hy,hxodd,hyodd,hsum4,hsum16,hsize⟩
  let p := (a4X t+a4Y t-4)/2
  let q := (a4X t+3*a4Y t-10)/4
  have hparent : RunReach p q := by
    simpa [RunReach,p,q] using
      (BB6.Agent3.oddodd_lowval_blank_reach_iff
        (a4X t) (a4Y t) hxodd hyodd hy hsum4 (by omega) hsize).mp hreach
  have hP8 : 8*(p+q)=38046615075*t+10202761387 := by
    dsimp [p,q,a4X,a4Y]
    omega
  have hQ8 : 8*q=18324830685*t+4914073813 := by
    dsimp [q,a4X,a4Y]
    omega
  have hPmod : (38046615075*t+10202761387)%32=8 := by omega
  have hQmod : (18324830685*t+4914073813)%16=8 := by omega
  have htmin : 31≤t := by omega
  have hpX : 5<p := by
    dsimp [p,a4X,a4Y]
    omega
  have hpY : 5≤q := by
    dsimp [q,a4X,a4Y]
    omega
  have hpOdd : q%2=1 := by omega
  have hpSum : (p+q)%4=1 := by omega
  exact (run_no_odd_sum_one p q hpX hpY hpOdd hpSum) hparent

/-- The corrected P7E1E residual is genuinely blank-unreachable on
    t = 31 (mod 32). Its complete even/even parent fan has only the
    direct parent D(t), and the exact odd-seven inverse takes D(t) to A4(t). -/
theorem p7e1e_unreachable_of_t_mod32_31 (t : Nat) (ht : t%32=31) :
    ¬ RunReach (p7e1eX t) (p7e1eY t) := by
  intro hreach
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
  obtain ⟨a,k,hprev,hstep⟩ :=
    run_parent_of_left_gt5 (p7e1eX t) (p7e1eY t) hx hreach
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
    have hDreach : RunReach (p7e1eDX t) (p7e1eDY t) := by
      simpa only [ha,hk,hDx,hDy] using hprev
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
    have hA4reach : RunReach (a4X t) (a4Y t) := by
      have hiff := (BB6.Agent3.odd_seven_blank_reach_iff
        (p7e1eDX t) (p7e1eDY t)
        hDxEven hDyOdd hDy5 hDmod hDsize).mp hDreach
      have hAx : (p7e1eDX t+p7e1eDY t-5)/2=a4X t := by
        dsimp [p7e1eDX,p7e1eDY,a4X]
        omega
      have hAy : (p7e1eDX t+3*p7e1eDY t-9)/4=a4Y t := by
        dsimp [p7e1eDX,p7e1eDY,a4Y]
        omega
      simpa [RunReach,hAx,hAy] using hiff
    exact (a4_unreachable_of_t_mod32_31 t ht) hA4reach
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

#print axioms a4_t31_facts
#print axioms a4_unreachable_of_t_mod32_31
#print axioms p7e1e_unreachable_of_t_mod32_31

end BB6.Agent3Root32HighStopA4


/-- On the t ≡ 31 (mod 32) slice, the accepted three-way root32
    reduction loses its P7E1E alternative and therefore leaves only
    the already-documented D0E and L obligations. -/
theorem root32_highstop_t31_reduces_to_two_residuals
    (r E u t : Nat)
    (hr64 : r%64=32)
    (hE : E=201+3360*(6657+8192*r))
    (hRoot : 18018+211*u+22155*r=20*2^(E-13))
    (hT : RunReach (1048576*u+70538) 3)
    (hu : u=1802+6720*t)
    (ht : t%32=31) :
    RunReach (1469153280*t+393975148) (2788638720*t+747814654) ∨
    RunReach (5065196640*t+1358307257) (990617040*t+265648583) := by
  obtain ⟨t',hu',hres⟩ :=
    BB6.Agent3Root32HighStopP7.root32_highstop_reduces_to_three_residuals
      r E u hr64 hE hRoot hT
  have hEq : t'=t := by omega
  rcases hres with hD0 | hL | hP7
  · exact Or.inl (by simpa [hEq] using hD0)
  · exact Or.inr (by simpa [hEq] using hL)
  · have hP7t : RunReach (p7e1eX t) (p7e1eY t) := by
      simpa [hEq,p7e1eX,p7e1eY] using hP7
    exact False.elim ((p7e1e_unreachable_of_t_mod32_31 t ht) hP7t)

/-- The root32 index congruence maps t ≡ 31 (mod 32) to
    r ≡ 352 (mod 2048). This labels the P7E1E residual exclusion only. -/
theorem p7_residual_root_index_class
    (r E t j : Nat)
    (hE : 30≤E)
    (hr : r=32+64*j)
    (hroot : 17300+22155*(t+j)=5*2^(E-17))
    (ht : t%32=31) :
    r%2048=352 := by
  have hmod :=
    BB6.Agent3Root32HighStopIndexMap.root32_tj_mod8192 t j E hE hroot
  have hj : j%32=5 := by omega
  rw [hr]
  omega
