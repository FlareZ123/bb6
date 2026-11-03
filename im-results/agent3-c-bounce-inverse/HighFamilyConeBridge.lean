import HighAffineCone
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- The previous m>=6 high-stop exclusion extends to all m congruent
    two modulo four, in particular the entire previously omitted m=2
    family. The high stopping equation itself supplies sufficient powers
    of two when j+3 is even. -/
theorem high_family_all_mod_four_in_cone (j m k : Nat)
    (hm4 : m%4=2)
    (hj : (j+127*m)%128=87)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3)%8=5 ∧ (2*(2*j+3)+k)%128=6 := by
  have hm2 : 2≤m := by omega
  have hjodd : 2∣j+3 := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  obtain ⟨q,hq⟩ := hjodd
  have hp64 : 64 ∣ 2^(2*m+2) := by
    change 2^6 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨p,hp⟩ := hp64
  have hd128 : 128 ∣ k+j+3*m+5 := by
    refine ⟨p*q, ?_⟩
    calc
      k+j+3*m+5 = 2^(2*m+2)*(j+3) := hgate
      _=(64*p)*(2*q) := by rw [hp,hq]
      _=128*(p*q) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hmod : (k+j+3*m+5)%128=0 := Nat.mod_eq_zero_of_dvd hd128
  omega

theorem high_halt_affine_m2plus_unreachable
    (j m k time : Nat)
    (hm4 : m%4=2)
    (hj : (j+127*m)%128=87)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (2*j+3,k) := by
  obtain ⟨hx,hy⟩ := high_family_all_mod_four_in_cone j m k hm4 hj hgate
  exact affine_three_cone_unreachable (2*j+3) k time hx hy

#print axioms high_family_all_mod_four_in_cone
#print axioms high_halt_affine_m2plus_unreachable
end BB6.Agent3
