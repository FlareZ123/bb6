import M32MassDepth
import M32SecondGeneralArithmetic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15

/-- The M32 finite quotient excludes all 32 parameter classes across
    all m≡3(mod4) sectors in the true second Machine C halting family,
    with unbounded odd affine-inverse depth d=2r+1. -/
theorem second_m32_all_mass_unreachable (m k r j q : Nat)
    (hm : m%4=3) (hr : r+3≤m) (hqj : q≤j)
    (hX : j+3*m+3=2^(2*r+2)*(2*q+1))
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hclass : m32SecondMassClass m r q) :
    ¬ CReach (2*j+3) k := by
  obtain ⟨Q,hQ,hform,ha,hmass,hmod⟩ :=
    second_m32_mass_structure m k r j q hm hr hqj hX hk
  have hcell := m32_mass_class_to_cells
    ((2*j+3)+2*k) m r q Q hmass hmod hclass
  have hc : BB6.Agent11.m32MassCell
      ((2*j+3)+2*k) (2*r+1) Q := by
    simpa only [BB6.Agent11.m32MassCell,
      BB6.Agent11.m32Cylinder, BB6.Agent15.m32Cylinder] using hcell
  have hcell' : BB6.Agent11.m32MassCell
      ((2*j+3)+2*(2^((2*r+1)+1)*(2*Q+1)-2)) (2*r+1) Q := by
    simpa only [←hform] using hc
  have hf := BB6.Agent11.original_m32_mass_barrier
    (2*j+3) (2*r+1) Q ha hQ hcell'
  simpa only [hform] using hf

#print axioms second_m32_all_mass_unreachable
end BB6.Agent15
