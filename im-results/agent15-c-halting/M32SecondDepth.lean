import M32AllDepthOriginal
import M32SecondArithmetic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15

/-- A new, arbitrary odd-affine-depth exclusion inside the exact second
    Machine C halting family. All quotient dependence is through the
    actual original-source M32 eight-cylinder Lean certificate. -/
theorem second_m32_original_unreachable (m k r j q : Nat)
    (hm : m%16=11) (hr : r+3≤m) (hqj : q≤j)
    (hX : j+3*m+3=2^(2*r+2)*(2*q+1))
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hclass : m32SecondParamClass r q) :
    ¬ CReach (2*j+3) k := by
  obtain ⟨Q,hQ,hform,ha,hmass,hdepth⟩ :=
    second_m32_arithmetic m k r j q hm hr hqj hX hk hclass
  have hc : BB6.Agent11.m32DepthClass (2*r+1) Q := by
    change m32SecondClass (2*r+1) Q
    exact hdepth
  have hforbid :=
    BB6.Agent11.original_m32_odd_depth_barrier
      (2*j+3) (2*r+1) Q ha hQ
      (by simpa only [hform] using hmass) hc
  simpa only [hform] using hforbid

/-- Every odd affine-inverse depth carries arbitrarily large authentic
    second-family stopping candidates which the blank-origin orbit
    provably never reaches. -/
theorem second_m32_original_unbounded (r lower : Nat) :
    ∃ m j k : Nat, lower≤m ∧
      k+j+3*m+5=2^(2*m+2)*(j+3) ∧
      ¬ CReach (2*j+3) k := by
  obtain ⟨m,j,k,q,hmlower,hm,hr,hqj,hX,hk,hclass⟩ :=
    second_m32_witness_indices r lower
  exact ⟨m,j,k,hmlower,hk,
    second_m32_original_unreachable m k r j q hm hr hqj hX hk hclass⟩

#print axioms second_m32_original_unreachable
#print axioms second_m32_original_unbounded
end BB6.Agent15
