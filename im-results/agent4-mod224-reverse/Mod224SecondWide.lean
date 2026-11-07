import Mod224Second

set_option maxHeartbeats 0

namespace A4Mod224

/-- The three distinct stable dyadic residues modulo 224 as the
    2m+2 exponent advances modulo six. -/
theorem pow_two_mod224_modzero (r : Nat) :
    (2:Nat)^(2*(3*r+3)+2) % 224 = 32 := by
  induction r with
  | zero => decide
  | succ r ih =>
      have he : 2*(3*(r+1)+3)+2 = (2*(3*r+3)+2)+6 := by omega
      rw [he,Nat.pow_add,Nat.mul_mod,ih]

theorem pow_two_mod224_modone (r : Nat) :
    (2:Nat)^(2*(3*r+4)+2) % 224 = 128 := by
  induction r with
  | zero => decide
  | succ r ih =>
      have he : 2*(3*(r+1)+4)+2 = (2*(3*r+4)+2)+6 := by omega
      rw [he,Nat.pow_add,Nat.mul_mod,ih]

theorem second_mod224_gate_m93 (j m k : Nat)
  (hj : j%224=5) (hm : m%672=93)
  (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
  (2*j+3)%224=13 ∧ k%224=191 := by
  have hform : ∃ r : Nat, m = 3*r+3 := ⟨(m-3)/3,by omega⟩
  obtain ⟨r,hr⟩ := hform
  have hpow : (2:Nat)^(2*m+2)%224=32 := by
    rw [hr]
    exact pow_two_mod224_modzero r
  have hrhs : ((2:Nat)^(2*m+2)*(j+3))%224=32 := by
    rw [Nat.mul_mod,hpow]
    omega
  have hlhs : (k+j+3*m+5)%224=32 := by rw [hstop]; exact hrhs
  constructor
  · omega
  · omega

theorem second_mod224_gate_m349 (j m k : Nat)
  (hj : j%224=5) (hm : m%672=349)
  (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
  (2*j+3)%224=13 ∧ k%224=191 := by
  have hform : ∃ r : Nat, m = 3*r+4 := ⟨(m-4)/3,by omega⟩
  obtain ⟨r,hr⟩ := hform
  have hpow : (2:Nat)^(2*m+2)%224=128 := by
    rw [hr]
    exact pow_two_mod224_modone r
  have hrhs : ((2:Nat)^(2*m+2)*(j+3))%224=128 := by
    rw [Nat.mul_mod,hpow]
    omega
  have hlhs : (k+j+3*m+5)%224=128 := by rw [hstop]; exact hrhs
  constructor
  · omega
  · omega

/-- The factor-seven inverse core forbids *three*, rather than one,
    complete infinite depth families of the source's second stopping
    equation: m modulo 672 in {29,93,349}. -/
theorem source_no_second_gate_three (j m k : Nat)
    (hj : j%224=5)
    (hm : m%672=29 ∨ m%672=93 ∨ m%672=349)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  intro hr
  rcases hm with hm29 | hm93 | hm349
  · exact source_no_second_gate_5_29 j m k hj hm29 hstop hr
  · obtain ⟨ha,hk⟩ := second_mod224_gate_m93 j m k hj hm93 hstop
    exact source_no_mod224_13_191 (2*j+3) k ha hk hr
  · obtain ⟨ha,hk⟩ := second_mod224_gate_m349 j m k hj hm349 hstop
    exact source_no_mod224_13_191 (2*j+3) k ha hk hr

#print axioms pow_two_mod224_modzero
#print axioms pow_two_mod224_modone
#print axioms second_mod224_gate_m93
#print axioms second_mod224_gate_m349
#print axioms source_no_second_gate_three

end A4Mod224
