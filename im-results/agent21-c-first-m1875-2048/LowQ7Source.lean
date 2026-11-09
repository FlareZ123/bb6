import Low1875Source
import LowQ7
import Lean.Elab.Tactic.Omega

namespace BB6.Agent21LowQ7

/-- Original blank return orbit excludes the deeper q=7 modulo16 low ray. -/
theorem blank_no_6995_low (time u : Nat) :
    BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠
      some (1,8192*u+3587) := by
  rw [BB6.Agent21Low1875.runF_eq_source]
  exact LocalQ7.runF_no_q7 BB6.Agent46.secNext
    (fun a k x y hy h => BB6.Agent21Low1875.source_inverse_is_pred a k x y hy h)
    time u

/-- Infinite first-stopping index m=6995 modulo 8192 is forbidden. -/
theorem first_stop_m6995_mod8192 (time m k : Nat)
    (hm : m%8192=6995) (hstop : k+3*m+4=2^(2*m+3)) :
    BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠
      some (1,k) := by
  have hmmin : 6995≤m := by omega
  have hpow : 8192 ∣ (2:Nat)^(2*m+3) := by
    change (2:Nat)^13 ∣ (2:Nat)^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hsum : (k+3*m+4)%8192=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hpow
  have hkmod : k%8192=3587 := by omega
  have hk : k=8192*(k/8192)+3587 := by omega
  rw [hk]
  exact blank_no_6995_low time (k/8192)

#print axioms blank_no_6995_low
#print axioms first_stop_m6995_mod8192
end BB6.Agent21LowQ7
