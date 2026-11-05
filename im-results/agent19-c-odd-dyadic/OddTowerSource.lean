import OddTowerGeneric
import OddTowerArithmetic
import OddTowerGeneralHigh
import EvenRightSixOrbit
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
namespace BB6.Agent19Tower

private theorem genuine_reverse (x y : Nat) (hy : 6≤y) (he : y%2=0)
    (h0 : (x+y)%8≠0) (h7 : (x+y)%8≠7) :
    BB6.Agent3.CReach x y →
    BB6.Agent3.CReach (x+y-2) ((y-2)/2) :=
  (BB6.Agent46.six_even_right_blank_reach_iff x y hy he h0 h7).mp

private theorem genuine_odd_no (x y : Nat) (hy : 5≤y)
    (ho : y%2=1) (hs : (x+y)%4=2) :
    ¬ BB6.Agent3.CReach x y := by
  rintro ⟨time,hr⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hr
      omega
  | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n x y hr hy ho
      omega

/-- Complete unbounded-depth dyadic forbidden family on authentic blank section. -/
theorem blank_no_alternating_dyadic (n x w : Nat)
    (hw : 7≤w) (hw4 : w%4=3)
    (hx : x%8=(if n%2=0 then 7 else 3)) :
    ¬ BB6.Agent3.CReach x (2^(n+2)*w-2) :=
  tower BB6.Agent3.CReach genuine_reverse genuine_odd_no n x w hw hw4 hx

/-- Concrete mod32 cylinder implied by the uniform unbounded-depth theorem. -/
theorem blank_no_high_three_mod32 (u v:Nat) (hv : 1≤v) :
    ¬ BB6.Agent3.CReach (8*u+3) (32*v+22) := by
  have hw : 7≤4*v+3 := by omega
  have hw4 : (4*v+3)%4=3 := by omega
  have hx : (8*u+3)%8=(if (1:Nat)%2=0 then 7 else 3) := by
    have hh : (8*u+3)%8=3 := by omega
    simpa using hh
  have hh:=blank_no_alternating_dyadic 1 (8*u+3) (4*v+3) hw hw4 hx
  have hy : 2^(1+2)*(4*v+3)-2=32*v+22 := by
    change 8*(4*v+3)-2=32*v+22
    omega
  rw [hy] at hh
  exact hh

/-- High stopping family with j divisible by four. -/
theorem blank_no_high_stop_depth_three (j m k:Nat)
    (hm : 3≤m) (hj : j%4=0)
    (hpair : (j+3*m+3)%32=8)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  obtain ⟨u,v,hv,hu,hk⟩ := high_three_arithmetic j m k hm hj hpair heq
  intro hr
  rw [hu,hk] at hr
  exact blank_no_high_three_mod32 u v hv hr

/-- All-exponent exclusion of authentic Machine C high stopping gateways.
    The stopping parameter's dyadic order forces a forbidden blank section
    at whatever exponent n occurs, without fixing a finite modulus. -/
theorem blank_no_high_stop_all_depth (n j m k:Nat)
    (hm : n+4≤2*m+2)
    (hpair : (j+3*m+3)%2^(n+4)=2^(n+2))
    (hj : (2*j+3)%8=(if n%2=0 then 7 else 3))
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  obtain ⟨w,hw,hw4,hk⟩ :=
    high_all_depth_arithmetic n j m k hm hpair heq
  intro hr
  rw [hk] at hr
  exact blank_no_alternating_dyadic n (2*j+3) w hw hw4 hj hr

#print axioms blank_no_alternating_dyadic
#print axioms blank_no_high_three_mod32
#print axioms blank_no_high_stop_depth_three
#print axioms blank_no_high_stop_all_depth
end BB6.Agent19Tower
