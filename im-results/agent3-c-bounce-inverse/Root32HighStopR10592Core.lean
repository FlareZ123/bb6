import Root32HighStopP7
import Root32HighStopA4Core
import Root32HighStopR10592LCore
import RRoot32ExceptionalCoreQ
import D0EInverseArithmetic
import EvenOddFourExact
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 10000000
set_option maxRecDepth 262144

namespace BB6.Agent3Root32HighStopR10592Core

open BB6.Agent46
open BB6.Agent15D0E

abbrev RunReach (x y : Nat) : Prop :=
  BB6.Agent3Root32HighStopIntegrated.RunReach x y

def goodEvenEven (p : Nat × Nat) : Prop :=
  5 < p.1 ∧ p.1 % 2 = 0 ∧ 6 ≤ p.2 ∧ p.2 % 2 = 0 ∧
  (p.1 + p.2) % 4 = 2

def e7State (t : Nat) : Nat × Nat :=
  (1756161120*t+470940530,2645134800*t+709331944)

def pState (t : Nat) : Nat × Nat :=
  (4401295920*t+1180272472,1322567400*t+354665971)

def rState (t : Nat) : Nat × Nat :=
  (2861931660*t+767469219,2092249530*t+561067594)

theorem d0e_intermediate_good (t : Nat) :
    goodEvenEven (d0e0 (1802+6720*t)) ∧
    goodEvenEven (d0e1 (1802+6720*t)) ∧
    goodEvenEven (d0e2 (1802+6720*t)) ∧
    goodEvenEven (d0e3 (1802+6720*t)) ∧
    goodEvenEven (d0e4 (1802+6720*t)) ∧
    goodEvenEven (d0e5 (1802+6720*t)) ∧
    goodEvenEven (d0e6 (1802+6720*t)) := by
  simp [goodEvenEven,d0e0,d0e1,d0e2,d0e3,d0e4,d0e5,d0e6] <;> omega

theorem even_even_sum2_reach_forces_direct (x y : Nat)
    (hx : 5 < x) (hxe : x%2=0)
    (hy : 6 ≤ y) (hye : y%2=0)
    (hsum : (x+y)%4=2)
    (hr : RunReach x y) :
    RunReach (x+y-2) ((y-2)/2) := by
  obtain ⟨a,k,hprev,hedge⟩ :=
    BB6.Agent3Root32HighStopIntegrated.run_parent_of_left_gt5 x y hx hr
  have hfan := BB6.Agent3ParentFan.even_even_parent_fan
    a k x y (by omega) hxe hy hye hedge
  rcases hfan with hdirect | hzero | hbounce
  · rcases hdirect with ⟨ha,hk⟩
    simpa [ha,hk] using hprev
  · rcases hzero with ⟨_,_,n,hxy,_⟩
    have hdiv : 4 ∣ x+y := by
      refine ⟨2^n*2,?_⟩
      rw [hxy]
      omega
    have hmod := Nat.mod_eq_zero_of_dvd hdiv
    omega
  · rcases hbounce with ⟨_,_,_,_,n,hnodd,hxy,_⟩
    have hn : 2 ≤ n+1 := by omega
    have hdivPow : 4 ∣ 2^(n+1) := by
      have h := Nat.pow_dvd_pow 2 hn
      simpa only [show (2:Nat)^2=4 by decide] using h
    have hdiv : 4 ∣ x+y := by
      rcases hdivPow with ⟨q,hq⟩
      refine ⟨q*(a+2),?_⟩
      calc
        x+y = 2^(n+1)*(a+2) := hxy
        _ = (4*q)*(a+2) := by rw [hq]
        _ = 4*(q*(a+2)) := by ac_rfl
    have hmod := Nat.mod_eq_zero_of_dvd hdiv
    omega

theorem even_even_direct_parent_reach (p : Nat × Nat)
    (hgood : goodEvenEven p)
    (hr : RunReach p.1 p.2) :
    RunReach (directParent p).1 (directParent p).2 := by
  rcases hgood with ⟨hx,hxe,hy,hye,hsum⟩
  have h := even_even_sum2_reach_forces_direct
    p.1 p.2 hx hxe hy hye hsum hr
  simpa [directParent] using h

theorem d0e0_reach_forces_d0e7 (t : Nat)
    (h0 : RunReach (d0e0 (1802+6720*t)).1
      (d0e0 (1802+6720*t)).2) :
    RunReach (d0e7 (1802+6720*t)).1
      (d0e7 (1802+6720*t)).2 := by
  let u := 1802+6720*t
  rcases d0e_intermediate_good t with ⟨g0,g1,g2,g3,g4,g5,g6⟩
  rcases d0e_direct_chain u with ⟨h01,h12,h23,h34,h45,h56,h67,_h78⟩
  have h1 : RunReach (d0e1 u).1 (d0e1 u).2 := by
    simpa only [h01] using even_even_direct_parent_reach (d0e0 u) g0 h0
  have h2 : RunReach (d0e2 u).1 (d0e2 u).2 := by
    simpa only [h12] using even_even_direct_parent_reach (d0e1 u) g1 h1
  have h3 : RunReach (d0e3 u).1 (d0e3 u).2 := by
    simpa only [h23] using even_even_direct_parent_reach (d0e2 u) g2 h2
  have h4 : RunReach (d0e4 u).1 (d0e4 u).2 := by
    simpa only [h34] using even_even_direct_parent_reach (d0e3 u) g3 h3
  have h5 : RunReach (d0e5 u).1 (d0e5 u).2 := by
    simpa only [h45] using even_even_direct_parent_reach (d0e4 u) g4 h4
  have h6 : RunReach (d0e6 u).1 (d0e6 u).2 := by
    simpa only [h56] using even_even_direct_parent_reach (d0e5 u) g5 h5
  simpa only [h67] using even_even_direct_parent_reach (d0e6 u) g6 h6

theorem d0e7_reach_fork (t : Nat)
    (hr : RunReach (d0e7 (1802+6720*t)).1
      (d0e7 (1802+6720*t)).2) :
    RunReach (d0e8 (1802+6720*t)).1 (d0e8 (1802+6720*t)).2 ∨
    RunReach (e7State t).1 (e7State t).2 := by
  let u := 1802+6720*t
  let x := (d0e7 u).1
  let y := (d0e7 u).2
  let S := 878080560*t+235470266
  let d8 : Nat × Nat := (x+y-2,(y-2)/2)
  let e7 : Nat × Nat := (2*S-2,(x+2*y-2*S-8)/2)
  obtain ⟨a,k,hprev,hedge⟩ :=
    BB6.Agent3Root32HighStopIntegrated.run_parent_of_left_gt5
      x y (by dsimp [x,u,d0e7]; omega) hr
  have hsum : x+y=8*S := by dsimp [x,y,S,u,d0e7]; omega
  have hS4 : S%4≠0 := by dsimp [S]; omega
  have hSgt : 2<S := by dsimp [S]; omega
  have hfan := BB6.Agent11M0SumZeroVerified.even_even_sumzero_parent
    a k x y S
    (by dsimp [x,u,d0e7]; omega)
    (by dsimp [x,u,d0e7]; omega)
    (by dsimp [y,u,d0e7]; omega)
    (by dsimp [y,u,d0e7]; omega)
    hsum hS4 hSgt hedge
  rcases hfan with hdirect | hbounce
  · rcases hdirect with ⟨ha,hk⟩
    have hD8reach : RunReach d8.1 d8.2 := by
      simpa [d8,ha,hk] using hprev
    have hD8eq : d8=d0e8 u := by
      apply Prod.ext
      · dsimp [d8,x,y,u,d0e7,d0e8]
        omega
      · dsimp [d8,x,y,u,d0e7,d0e8]
        omega
    exact Or.inl (by simpa [hD8eq] using hD8reach)
  · rcases hbounce with ⟨ha,hk⟩
    have hE7reach : RunReach e7.1 e7.2 := by
      simpa [e7,ha,hk] using hprev
    have hE7eq : e7=e7State t := by
      apply Prod.ext
      · dsimp [e7,x,y,S,u,d0e7,e7State]
        omega
      · dsimp [e7,x,y,S,u,d0e7,e7State]
        omega
    exact Or.inr (by simpa [hE7eq] using hE7reach)

theorem d0e8_unreachable (t : Nat) :
    ¬ RunReach (d0e8 (1802+6720*t)).1
      (d0e8 (1802+6720*t)).2 := by
  let u := 1802+6720*t
  let x := (d0e8 u).1
  let y := (d0e8 u).2
  let a := 3517768800*t+943341635
  let k := 1764330960*t+473131391
  have hx : x%2=0 := by dsimp [x,u,d0e8]; omega
  have hy : y%2=1 := by dsimp [y,u,d0e8]; omega
  have hy5 : 5≤y := by dsimp [y,u,d0e8]; omega
  have hmod : (x+y+1)%8=4 := by dsimp [x,y,u,d0e8]; omega
  have hA : 2*a+6=x+y+1 := by dsimp [a,x,y,u,d0e8]; omega
  have hK : 2*k+a+7=x+2*y := by dsimp [a,x,y,u,d0e8]; omega
  have haOdd : a%2=1 := by dsimp [a]; omega
  have hkOdd : k%2=1 := by dsimp [k]; omega
  have hk5 : 5≤k := by dsimp [k]; omega
  have hsum : (a+k)%4=2 := by dsimp [a,k]; omega
  have hpa : (x+y-5)/2=a := by omega
  have hpk : (x+3*y-9)/4=k := by omega
  intro hr
  have hiff := BB6.Agent3.evenodd_four_blank_reach_iff x y hx hy hy5 hmod
  have hparent : RunReach a k := by
    simpa [RunReach,BB6.Agent3Root32HighStopIntegrated.RunReach,hpa,hpk]
      using hiff.mp hr
  exact (BB6.Agent3Root32HighStopIntegrated.run_no_odd_sum_two
    a k (by dsimp [a]; omega) hk5 hkOdd hsum) hparent

theorem e7_unreachable_t31 (t : Nat) (ht : t%256=31) :
    ¬ RunReach (e7State t).1 (e7State t).2 := by
  let q := t/4
  have hgood : goodEvenEven (e7State t) := by
    simp [goodEvenEven,e7State] <;> omega
  intro hE7
  have hP : directParent (e7State t)=pState t := by
    apply Prod.ext
    · dsimp [directParent,e7State,pState]
      omega
    · dsimp [directParent,e7State,pState]
      omega
  have hPReach : RunReach (pState t).1 (pState t).2 := by
    simpa only [hP] using even_even_direct_parent_reach
      (e7State t) hgood hE7
  have hPx : (pState t).1%2=0 := by dsimp [pState]; omega
  have hPy : (pState t).2%2=1 := by dsimp [pState]; omega
  have hPy5 : 5≤(pState t).2 := by dsimp [pState]; omega
  have hPmod : ((pState t).1+(pState t).2+1)%8=4 := by
    dsimp [pState]
    omega
  have hpa : ((pState t).1+(pState t).2-5)/2=(rState t).1 := by
    dsimp [pState,rState]
    omega
  have hpk : ((pState t).1+3*(pState t).2-9)/4=(rState t).2 := by
    dsimp [pState,rState]
    omega
  have hiff := BB6.Agent3.evenodd_four_blank_reach_iff
    (pState t).1 (pState t).2 hPx hPy hPy5 hPmod
  have hRReach : RunReach (rState t).1 (rState t).2 := by
    simpa [RunReach,BB6.Agent3Root32HighStopIntegrated.RunReach,hpa,hpk]
      using hiff.mp hPReach
  have hmod4 : t%4=3 := by omega
  have hdiv4 : t%4+4*(t/4)=t := Nat.mod_add_div t 4
  have hdiv64 : (t/4)%64+64*((t/4)/64)=t/4 :=
    Nat.mod_add_div (t/4) 64
  have ht4 : t=4*q+3 := by dsimp [q]; omega
  have hq : q%64=7 := by dsimp [q]; omega
  have hRx : (rState t).1=BB6.Agent3RRoot32ParentFanQ.RxQ q := by
    rw [ht4]
    dsimp [rState,BB6.Agent3RRoot32ParentFanQ.RxQ]
    omega
  have hRy : (rState t).2=BB6.Agent3RRoot32ParentFanQ.RyQ q := by
    rw [ht4]
    dsimp [rState,BB6.Agent3RRoot32ParentFanQ.RyQ]
    omega
  have hRReachQ : RunReach
      (BB6.Agent3RRoot32ParentFanQ.RxQ q)
      (BB6.Agent3RRoot32ParentFanQ.RyQ q) := by
    simpa only [hRx,hRy] using hRReach
  have hRReachQ' :
      BB6.Agent3RRoot32ExceptionalCoreQ.RunReach
        (BB6.Agent3RRoot32ParentFanQ.RxQ q)
        (BB6.Agent3RRoot32ParentFanQ.RyQ q) := by
    simpa [RunReach,BB6.Agent3Root32HighStopIntegrated.RunReach,
      BB6.Agent3RRoot32ExceptionalCoreQ.RunReach] using hRReachQ
  exact (BB6.Agent3RRoot32ExceptionalCoreQ.R_unreachable_q7 q hq) hRReachQ'

theorem d0e_unreachable_t31 (t : Nat) (ht : t%256=31) :
    ¬ RunReach (d0e0 (1802+6720*t)).1
      (d0e0 (1802+6720*t)).2 := by
  intro hD0
  have hD7 := d0e0_reach_forces_d0e7 t hD0
  rcases d0e7_reach_fork t hD7 with hD8 | hE7
  · exact d0e8_unreachable t hD8
  · exact e7_unreachable_t31 t ht hE7

theorem root32_highstop_r10592_unreachable
    (r E u : Nat)
    (hE : E=201+3360*(6657+8192*r))
    (hRoot : 18018+211*u+22155*r=20*2^(E-13))
    (hr10592 : r%16384=10592) :
    ¬ RunReach (1048576*u+70538) 3 := by
  have hr64 : r%64=32 := by omega
  obtain ⟨t,hu⟩ :=
    BB6.Agent3U5B2Root32ParameterBridge.root32_u_parameter_of_exact
      r E u hr64 hE hRoot
  let j := r/64
  have hrj : r=32+64*j := by
    dsimp [j]
    have h := Nat.mod_add_div r 64
    omega
  let q := r/16384
  have hrq : r=16384*q+10592 := by
    dsimp [q]
    have h := Nat.mod_add_div r 16384
    omega
  have hjExact : j=256*q+165 := by
    dsimp [j]
    rw [hrq]
    dsimp [q]
    omega
  have hj : j%256=165 := by rw [hjExact]; omega
  have hE17 : 17≤E := by rw [hE]; omega
  have hRoot' :
      18018+211*(1802+6720*t)+22155*r=20*2^(E-13) := by
    simpa [hu] using hRoot
  have hTj : 17300+22155*(t+j)=5*2^(E-17) :=
    root32_tj_exact t j E r hrj hRoot' hE17
  have hE8 : 8≤E-17 := by rw [hE]; omega
  have hdivPow : 256∣2^(E-17) := by
    have h := Nat.pow_dvd_pow 2 hE8
    simpa only [show (2:Nat)^8=256 by decide] using h
  have hdiv : 256∣5*2^(E-17) := by
    rcases hdivPow with ⟨p,hp⟩
    refine ⟨5*p,?_⟩
    rw [hp]
    ac_rfl
  have hleftDiv : 256∣17300+22155*(t+j) := by
    rw [hTj]
    exact hdiv
  have hmod := Nat.mod_eq_zero_of_dvd hleftDiv
  have h148 : (17300:Nat)%256=148 := by decide
  have h139 : (22155:Nat)%256=139 := by decide
  have hnorm : (148+139*((t+j)%256))%256=0 := by
    simpa [Nat.add_mod,Nat.mul_mod,h148,h139] using hmod
  have hdivNorm : 256∣148+139*((t+j)%256) :=
    Nat.dvd_iff_mod_eq_zero.mpr hnorm
  rcases hdivNorm with ⟨z,hz⟩
  have hreslt : (t+j)%256<256 := Nat.mod_lt (t+j) (by decide)
  have htjMod : (t+j)%256=196 := by omega
  have hsumMod : (t%256+j%256)%256=196 := by
    simpa [Nat.add_mod] using htjMod
  have ht256 : t%256=31 := by omega
  have ht32 : t%32=31 := by omega
  intro hT
  have hres3 :=
    BB6.Agent3Root32HighStopP7.root32_highstop_reduces_to_three_residuals
      r E u hr64 hE hRoot hT
  rcases hres3 with ⟨t',hu',hbranches⟩
  have htEq : t'=t := by omega
  subst t'
  rcases hbranches with hD0 | hL | hP7
  · have hD0x : 1469153280*t+393975148=
        (d0e0 (1802+6720*t)).1 := by
      dsimp [d0e0]
      omega
    have hD0y : 2788638720*t+747814654=
        (d0e0 (1802+6720*t)).2 := by
      dsimp [d0e0]
      omega
    have hD0Reach : RunReach
        (d0e0 (1802+6720*t)).1 (d0e0 (1802+6720*t)).2 := by
      simpa only [hD0x,hD0y] using hD0
    exact d0e_unreachable_t31 t ht256 hD0Reach
  · have hLReach : RunReach
        (BB6.Agent3Root32HighStopR10592LCore.Lx t)
        (BB6.Agent3Root32HighStopR10592LCore.Ly t) := by
      simpa [BB6.Agent3Root32HighStopR10592LCore.Lx,
        BB6.Agent3Root32HighStopR10592LCore.Ly] using hL
    let m := t/32
    have htDecomp : t=32*m+31 := by
      dsimp [m]
      have h := Nat.mod_add_div t 32
      omega
    have hLnot :
        ¬ RunReach (BB6.Agent3Root32HighStopR10592LCore.Lx t)
          (BB6.Agent3Root32HighStopR10592LCore.Ly t) := by
      have h := BB6.Agent3Root32HighStopR10592LCore.L_unreachable_t31_mod32 m
      simpa [htDecomp] using h
    exact hLnot hLReach
  · exact (BB6.Agent3Root32HighStopA4Core.p7e1e_unreachable_of_t_mod32_31
      t ht32) hP7

#print axioms d0e0_reach_forces_d0e7
#print axioms d0e7_reach_fork
#print axioms d0e8_unreachable
#print axioms e7_unreachable_t31
#print axioms d0e_unreachable_t31
#print axioms root32_highstop_r10592_unreachable

end BB6.Agent3Root32HighStopR10592Core
