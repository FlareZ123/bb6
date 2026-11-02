import C48Reach
import FeederOrbitGeneric
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Genuine blank-section states of the form (1,1024q+772) are
    unreachable. The entire quantified q family is covered. -/
theorem blank_no_c48_one_gate (q : Nat) :
    ¬BB6.Agent3.CReach 1 (1024*q+772) := by
  intro h
  have ht : 1≤64*q+48 := by omega
  have hk : 1024*q+772=16*(64*q+48)+4 := by omega
  rw [hk] at h
  obtain ⟨time,hr⟩ :=
    (BB6.Agent3.generic_one_gate_reach_iff (64*q+48) ht).mp h
  have hx : 12*(64*q+48)=768*q+576 := by omega
  have hy : 10*(64*q+48)-1=640*q+479 := by omega
  rw [hx,hy] at hr
  exact blank_no_c48_target q time hr

/-- Every possible low Machine C halting section whose exponential
    parameter is 424 modulo 1024 is absent from the real blank orbit. -/
theorem blank_no_low_halt_depth424 (m k : Nat)
    (hm : m%1024=424)
    (heq : k+3*m+4=2^(2*m+3)) :
    ¬BB6.Agent3.CReach 1 k := by
  have hlarge : 4≤m := by omega
  have hpow : 1024 ∣ 2^(2*m+3) := by
    change 2^10 ∣ 2^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨w,hw⟩ := hpow
  have hmod : k%1024=772 := by omega
  have hk : k=1024*(k/1024)+772 := by omega
  intro h
  rw [hk] at h
  exact blank_no_c48_one_gate (k/1024) h

#print axioms blank_no_c48_one_gate
#print axioms blank_no_low_halt_depth424
end BB6.Agent46
