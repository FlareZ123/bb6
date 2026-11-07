import HighDyadicArithmetic
import DyadicSixCone
import OddOddLowVal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19HighDyadic

/-- Original-source, all-time exclusion of a high stopping family for
    Machine C. No finite cutoff or quotient assumption. -/
theorem high_dyadic_no_blank (j m k : Nat)
    (hm3 : 3≤m) (hm4 : m%4=3)
    (hpair : (j+9*m+14)%64=48)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  let x := 2*j+3
  let a := (x+k-4)/2
  let b := (x+3*k-10)/4
  let u := (b+2)/4
  obtain ⟨hy,hy5,h8,hsize,hxa,hxb,hbu,hu4,hu9,hmass⟩ :
      k%2=1 ∧ 5≤k ∧ (x+k)%8=4 ∧ 24≤x+k ∧
      x+k=2*a+4 ∧ x+3*k=4*b+10 ∧
      b+2=4*u ∧ u%4=1 ∧ 9≤u ∧
      (a+2*b+8)%8=0 := by
    simpa only [x,a,b,u] using finalArithmetic j m k hm3 hm4 hpair hstop
  have hx : x%2=1 := by dsimp [x]; omega
  have h4 : (x+k)%4=0 := by omega
  have h16 : (x+k)%16≠0 := by omega
  intro hr
  have hparent : BB6.Agent3.CReach a b := by
    exact (BB6.Agent3.oddodd_lowval_blank_reach_iff
      x k hx hy hy5 h4 h16 hsize).mp hr
  have hb : b+2=(2:Nat)^2*u := by
    have : (2:Nat)^2=4 := by decide
    rw [this]
    exact hbu
  exact (BB6.Agent19SixCone.dyadic_six_cone_no_blank
    2 a b u hu9 hu4 hb hmass) hparent

/-- The parameterized high target is an explicit natural number, with
    no subtraction-truncation ambiguity. -/
theorem high_dyadic_stopping_target_unreachable (j m : Nat)
    (hm3 : 3≤m) (hm4 : m%4=3)
    (hpair : (j+9*m+14)%64=48) :
    ¬ BB6.Agent3.CReach (2*j+3)
      (2^(2*m+2)*(j+3)-(j+3*m+5)) := by
  let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
  have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
    dsimp [k]
    have he : j+3*m+5≤2^(2*m+2)*(j+3) := by
      have hp : 8*m+8≤2^(2*m+2) :=
        eight_power_bound m (by omega)
      have hpos : 1≤2^(2*m+2) := Nat.pow_pos (by decide)
      have hj : j≤2^(2*m+2)*j := by
        simpa using Nat.mul_le_mul_right j hpos
      have ht : 3*(8*m+8)≤3*2^(2*m+2) := by omega
      rw [Nat.mul_add]
      omega
    exact Nat.sub_add_cancel he
  exact high_dyadic_no_blank j m k hm3 hm4 hpair hstop

#print axioms high_dyadic_no_blank
#print axioms high_dyadic_stopping_target_unreachable
end BB6.Agent19HighDyadic
