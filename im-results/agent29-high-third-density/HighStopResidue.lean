import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29HighThird

/-- Exact high-family stopping equation, reduced at every dyadic precision
    bounded by the stopping exponent. Independent of section simulation. -/
theorem high_stop_mod_pow
    (j m k N : Nat) (hN : N ≤ 2*m+2)
    (hstop : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3)) :
    (k+j+3*m+5) % 2^N = 0 ∧
    (k+2*j+3+3*m+2) % 2^N = j % 2^N := by
  have hd : (2:Nat)^N ∣ (2:Nat)^(2*m+2) :=
    Nat.pow_dvd_pow 2 hN
  have hp : (2:Nat)^N ∣ (2:Nat)^(2*m+2)*(j+3) := by
    obtain ⟨q,hq⟩ := hd
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    ac_rfl
  have hmod : (k+j+3*m+5)%2^N=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hp
  constructor
  · exact hmod
  · calc
      (k+2*j+3+3*m+2)%2^N = ((k+j+3*m+5)+j)%2^N := by
        congr 1
        omega
      _ = ((k+j+3*m+5)%2^N+j%2^N)%2^N := by rw [Nat.add_mod]
      _ = j%2^N := by simp [hmod]

/-- For all m≥8, high stopping targets have a purely linear residue
    signature modulo 2^17. -/
theorem high_stop_mod_131072
    (j m k : Nat) (hm:8≤m)
    (hstop : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3)) :
    (k+j+3*m+5)%131072=0 ∧
    (k+2*j+3+3*m+2)%131072=j%131072 := by
  have h := high_stop_mod_pow j m k 17 (by omega) hstop
  simpa only [show (2:Nat)^17=131072 by decide] using h

#print axioms high_stop_mod_pow
#print axioms high_stop_mod_131072
end BB6.Agent29HighThird
