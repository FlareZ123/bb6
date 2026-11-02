import P1R54Blocked
import P1R54Gap
import P1R54Identity
import P1CriticalArithmetic
import P1Gate

namespace BB6.Agent47P1

/-- An original-source, all-time no-blank-reach theorem for the critical
G hub at EVERY n=65536*q+54, not a finite simulation sample. -/
theorem r54_no_hub (q : Nat) :
    ¬ BB6.Agent1.Reach
      (14*2^(65536*q+54)-2*(65536*q+54)-16) 3 := by
  have hc := r54root_blocked (r54S q)
    (r54_gap0 q) (r54_gap1 q) (r54_gap2 q)
  have hno := BB6.Agent4Cone.blocked_no_reach _ _ hc
  have heq := r54_root_identity q
  rw [heq] at hno
  simpa [r54b0d] using hno

/-- Infinite blank-halting-gateway exclusion for a P1 critical residue
outside the previously certified n ≡ 10 (mod 16) family. -/
theorem blank_no_critical_54_mod65536 (q : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(65536*q+54)-2*(65536*q+54)-10) := by
  let n := 65536*q+54
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
  exact (r54_no_hub q) (by simpa [n] using hhub)

#print axioms r54_no_hub
#print axioms blank_no_critical_54_mod65536
end BB6.Agent47P1
