import HighDyadicAllDepthArithmetic
import DyadicSixCone
import OddOddLowVal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19AllDepth

/-- For arbitrary dyadic inverse depth r, the authentic blank-derived
    high stopping target is excluded whenever it lies in the exact
    all-depth missing inverse cone. No finite-state abstraction occurs. -/
theorem high_depth_no_blank (r j m k : Nat)
    (hr : 2≤r) (hm : 3≤m)
    (hdepth : r+4≤2*m+2)
    (hm4 : m%4=(2*r+3)%4)
    (hpair : (j+9*m+14)%2^(r+4)=3*2^(r+2))
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  let x := 2*j+3
  let a := (x+k-4)/2
  let b := (x+3*k-10)/4
  let u := (b+2)/2^r
  obtain ⟨hy,h8,hsize,hy5,hxa,hxb,hbu,hu4,hu9,hmass⟩ :
      k%2=1 ∧ (x+k)%8=4 ∧ 24≤x+k ∧ 5≤k ∧
      x+k=2*a+4 ∧ x+3*k=4*b+10 ∧
      b+2=2^r*u ∧ u%4=1 ∧ 9≤u ∧
      (a+2*b+4*r)%8=0 := by
    simpa only [x,a,b,u] using
      powered_depth_core r j m k hr hm hdepth hm4 hpair hstop
  have hx : x%2=1 := by dsimp [x]; omega
  have h4 : (x+k)%4=0 := by omega
  have h16 : (x+k)%16≠0 := by omega
  intro hrch
  have hparent : BB6.Agent3.CReach a b :=
    (BB6.Agent3.oddodd_lowval_blank_reach_iff x k
      hx hy hy5 h4 h16 hsize).mp hrch
  exact (BB6.Agent19SixCone.dyadic_six_cone_no_blank
    r a b u hu9 hu4 hbu hmass) hparent

/-- Explicit all-natural-parameter high stopping targets with r not fixed.
    This contains the previously verified r=2 residue cylinder. -/
theorem high_depth_stopping_target_no_blank (r j m : Nat)
    (hr : 2≤r) (hm : 3≤m)
    (hdepth : r+4≤2*m+2)
    (hm4 : m%4=(2*r+3)%4)
    (hpair : (j+9*m+14)%2^(r+4)=3*2^(r+2)) :
    ¬ BB6.Agent3.CReach (2*j+3)
      (2^(2*m+2)*(j+3)-(j+3*m+5)) := by
  let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
  have he : j+3*m+5≤2^(2*m+2)*(j+3) := by
    have hp : 8*m+8≤2^(2*m+2) :=
      BB6.Agent19HighDyadic.eight_power_bound m (by omega)
    have hpos : 1≤2^(2*m+2) := Nat.pow_pos (by decide)
    have hj : j≤2^(2*m+2)*j := by
      simpa using Nat.mul_le_mul_right j hpos
    have ht : 3*(8*m+8)≤3*2^(2*m+2) := by omega
    rw [Nat.mul_add]
    omega
  have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
    dsimp [k]
    have hh := Nat.sub_add_cancel he
    omega
  exact high_depth_no_blank r j m k hr hm hdepth hm4 hpair hstop

#print axioms high_depth_no_blank
#print axioms high_depth_stopping_target_no_blank
end BB6.Agent19AllDepth
