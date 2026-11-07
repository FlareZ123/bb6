import Mod224Core

set_option maxHeartbeats 0

namespace A4Mod224

/-- For every natural r, the dyadic contribution to the second
    stopping equation is 64 modulo 224 at depth m=3r+2. -/
theorem pow_two_mod224_modthree (r : Nat) :
    (2:Nat)^(2*(3*r+2)+2) % 224 = 64 := by
  induction r with
  | zero => decide
  | succ r ih =>
      have he : 2*(3*(r+1)+2)+2 = (2*(3*r+2)+2)+6 := by omega
      rw [he,Nat.pow_add,Nat.mul_mod,ih]

/-- Infinite source-stopping parameter family selected by our c=0
    reverse core: j=5 mod 224 and m=29 mod 672. -/
theorem second_mod224_gate (j m k : Nat)
  (hj : j%224=5) (hm : m%672=29)
  (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
  (2*j+3)%224=13 ∧ k%224=191 := by
  have hform : ∃ r : Nat, m = 3*r+2 := ⟨(m-2)/3,by omega⟩
  obtain ⟨r,hr⟩ := hform
  have hpow : (2:Nat)^(2*m+2)%224=64 := by
    rw [hr]
    exact pow_two_mod224_modthree r
  have hrhs : ((2:Nat)^(2*m+2)*(j+3))%224=64 := by
    rw [Nat.mul_mod,hpow]
    omega
  have hlhs : (k+j+3*m+5)%224=64 := by rw [hstop]; exact hrhs
  constructor
  · omega
  · omega

/-- Every genuine source Machine C second-family stopping input with
    j≡5 modulo 224, m≡29 modulo 672 is absent from the blank orbit. -/
theorem source_no_second_gate_5_29 (j m k : Nat)
    (hj : j%224=5) (hm : m%672=29)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hr : BB6CLine.Reach (2*j+3,k,0)) : False := by
  obtain ⟨ha,hk⟩ := second_mod224_gate j m k hj hm hstop
  exact source_no_mod224_13_191 (2*j+3) k ha hk hr

#print axioms pow_two_mod224_modthree
#print axioms second_mod224_gate
#print axioms source_no_second_gate_5_29

end A4Mod224
