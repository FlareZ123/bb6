import U5B2Root32
import EvenEvenParentFan
import OddSevenOrbit
import OddOddLowVal
import Agent3CImage
import Root32HighStopIndexMap
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

namespace BB6.Agent3Root32HighStopA4Core
open BB6.Agent46

def RunReach (x y : Nat) : Prop :=
  ∃ n, BB6.Agent8Section.run secNext n (some (5,1)) = some (x,y)

theorem run_parent_of_left_gt5 (x y : Nat) (hx : 5<x)
    (hr : RunReach x y) :
    ∃ a k, RunReach a k ∧ secNext (a,k)=some (x,y) := by
  rcases hr with ⟨time,ht⟩
  cases time with
  | zero => simp [BB6.Agent8Section.run] at ht; omega
  | succ n =>
    cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at ht
    | some p =>
      rcases p with ⟨a,k⟩
      refine ⟨a,k,⟨n,hp⟩,?_⟩
      simpa [BB6.Agent8Section.run,hp] using ht

theorem run_no_odd_sum_two (x y : Nat)
    (_hx : 5<x) (hy : 5≤y) (ho : y%2=1)
    (hsum : (x+y)%4=2) : ¬ RunReach x y := by
  intro hr
  rcases hr with ⟨time,ht⟩
  cases time with
  | zero => simp [BB6.Agent8Section.run] at ht; omega
  | succ n =>
    have hi := BB6.Agent3.blank_section_odd_image n x y ht hy ho
    omega

theorem run_no_odd_sum_one (x y : Nat)
    (_hx : 5<x) (hy : 5≤y) (ho : y%2=1)
    (hsum : (x+y)%4=1) : ¬ RunReach x y := by
  intro hr
  rcases hr with ⟨time,ht⟩
  cases time with
  | zero => simp [BB6.Agent8Section.run] at ht; omega
  | succ n =>
    have hi := BB6.Agent3.blank_section_odd_image n x y ht hy ho
    omega

def a4X (t : Nat) : Nat := 2814461475*t + 754739388
def a4Y (t : Nat) : Nat := (4231969245*t + 1134865019)/2
def p7e1eX (t : Nat) : Nat := 1376399640*t + 369101882
def p7e1eY (t : Nat) : Nat := 2835015540*t + 760251268
def p7e1eDX (t : Nat) : Nat := 4211415180*t + 1129353148
def p7e1eDY (t : Nat) : Nat := 1417507770*t + 380125633

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

theorem a4_unreachable_of_t_mod32_31 (t : Nat) (ht : t%32=31) :
    ¬ RunReach (a4X t) (a4Y t) := by
  intro hreach
  rcases a4_t31_facts t ht with
    ⟨_hx,hy,hxodd,hyodd,hsum4,hsum16,hsize⟩
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
      simp
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

/-- The exact root-index equation maps this t-slice to r = 352 mod 2048.
This is an index identification, not a reachability assertion. -/
theorem p7_residual_root_index_class (r E t j : Nat)
    (hE : 30≤E)
    (hr : r=32+64*j)
    (hroot : 17300+22155*(t+j)=5*2^(E-17))
    (ht : t%32=31) : r%2048=352 := by
  have hmod :=
    BB6.Agent3Root32HighStopIndexMap.root32_tj_mod8192 t j E hE hroot
  have hj : j%32=5 := by omega
  rw [hr]
  omega

#print axioms p7_residual_root_index_class

end BB6.Agent3Root32HighStopA4Core
