import Mod240NewCore
import Mod240Second

set_option maxHeartbeats 0

namespace A4Mod240New

/-- A genuinely different parameter family from the modulo-four
    exclusion: j ≡ 11 (mod 240), m ≡ 11 (mod 80).
    Its second stopping input is (25,175) modulo 240. -/
theorem second_mod240_gate (j m k : Nat)
    (hj : j%240=11) (hm : m%80=11)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3)%240=25 ∧ k%240=175 := by
  have hform : ∃ r : Nat, m=2*r+3 := ⟨(m-3)/2,by omega⟩
  obtain ⟨r,hr⟩ := hform
  have hpow : (2:Nat)^(2*m+2)%240=16 := by
    rw [hr]
    exact A4Mod240.pow_two_mod240_odd_large r
  have hrhs : ((2:Nat)^(2*m+2)*(j+3))%240=224 := by
    rw [Nat.mul_mod,hpow]
    omega
  have hlhs : (k+j+3*m+5)%240=224 := by rw [hstop]; exact hrhs
  constructor
  · omega
  · omega

/-- Source-connected all-time result:
    every genuine second-family stopping input with j=11 mod 240 and
    m=11 mod 80 is absent from Machine C's accelerated blank orbit. -/
theorem source_no_second_gate_11_11 (j m k : Nat)
    (hj : j%240=11) (hm : m%80=11)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hr : BB6CLine.Reach (2*j+3,k,0)) : False := by
  obtain ⟨ha,hk⟩ := second_mod240_gate j m k hj hm hstop
  exact source_no_mod240_25_175 (2*j+3) k ha hk hr

#print axioms second_mod240_gate
#print axioms source_no_second_gate_11_11

end A4Mod240New
