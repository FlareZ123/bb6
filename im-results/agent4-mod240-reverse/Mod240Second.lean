import Mod240Core

set_option maxHeartbeats 0

namespace A4Mod240

/-- The unusually simple residue of the dyadic stopping term:
    at every odd depth m=2r+3 the power of two is 16 modulo 240. -/
theorem pow_two_mod240_odd_large (r : Nat) :
    (2:Nat)^(2*(2*r+3)+2) % 240 = 16 := by
  induction r with
  | zero => decide
  | succ r ih =>
      have he : 2*(2*(r+1)+3)+2 = (2*(2*r+3)+2)+4 := by omega
      rw [he,Nat.pow_add,Nat.mul_mod,ih]

/-- The exact published second-family halting equation selects our
    genuinely unreachable source cylinder on an infinite product of
    depth and first-counter parameter congruence classes. -/
theorem second_mod240_gate (j m k : Nat)
    (hj : j%240=1) (hm : m%80=3)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3)%240=5 ∧ k%240=49 := by
  have hform : ∃ r : Nat, m=2*r+3 := ⟨(m-3)/2,by omega⟩
  obtain ⟨r,hr⟩ := hform
  have hpow : (2:Nat)^(2*m+2)%240=16 := by
    rw [hr]
    exact pow_two_mod240_odd_large r
  have hrhs : ((2:Nat)^(2*m+2)*(j+3))%240=64 := by
    rw [Nat.mul_mod,hpow]
    omega
  have hlhs : (k+j+3*m+5)%240=64 := by rw [hstop]; exact hrhs
  constructor
  · omega
  · omega

/-- Unconditional source-accelerator exclusion for every second-family
    stopping input with j≡1 (mod 240) and m≡3 (mod 80). The true blank
    orbit cannot meet this family at any time. -/
theorem source_no_second_gate_1_3 (j m k : Nat)
    (hj : j%240=1) (hm : m%80=3)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hr : BB6CLine.Reach (2*j+3,k,0)) : False := by
  obtain ⟨ha,hk⟩ := second_mod240_gate j m k hj hm hstop
  exact source_no_mod240_5_49 (2*j+3) k ha hk hr

#print axioms pow_two_mod240_odd_large
#print axioms second_mod240_gate
#print axioms source_no_second_gate_1_3

end A4Mod240
