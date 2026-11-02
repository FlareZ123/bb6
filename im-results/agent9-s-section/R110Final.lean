import R110Proof
import P1CriticalArithmetic
import P1Gate

namespace BB6.Agent47P1
/-- Exclusion of one infinite 512-index family from genuine P1 halting gateways. -/
theorem blank_no_critical_110_mod512 (h:Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(512*h+110)-2*(512*h+110)-10) := by
  let n := 512*h+110
  have hn : 4≤n := by dsimp [n]; omega
  have he : n%2=0 := by dsimp [n]; omega
  obtain ⟨hl,hm⟩ := critical_even_target_form n hn he
  intro hr
  have hhub := BB6.Agent50P1.critical_target_implies_three
    (14*2^n-2*n-10) hl hm hr
  have heq : (14*2^n-2*n-10)-6 = 14*2^n-2*n-16 := by
    have hpow := n_plus_two_lt_pow n hn
    omega
  rw [heq] at hhub
  exact (r110_no_actual_hub h) (by simpa [n] using hhub)

#print axioms blank_no_critical_110_mod512
end BB6.Agent47P1
