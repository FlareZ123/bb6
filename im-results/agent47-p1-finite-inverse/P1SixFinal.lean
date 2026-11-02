import P1SixBlocked
import P1SixGap
import P1CriticalArithmetic
import P1Gate

namespace BB6.Agent47P1

/-- Every index congruent 6 modulo 16 has a three-hub finite inverse cone
whose leaves are all blocked by source-level global blank invariants. -/
theorem six_no_hub (h : Nat) :
    ¬ BB6.Agent1.Reach
      (14*2^(16*h+6)-2*(16*h+6)-16) 3 := by
  have hc := sixroot_blocked (sixU h) (sixU_lower h)
    (six_gap0 h) (six_gap1 h) (six_gap2 h)
  have hno := BB6.Agent4Cone.blocked_no_reach _ _ hc
  have heq : sixb0 (sixU h) = 14*2^(16*h+6)-2*(16*h+6)-16 := by
    simpa only [sixb0] using six_root_identity h
  rw [heq] at hno
  simpa [sixb0d] using hno

/-- Entire infinite P1 halting-critical residue n ≡ 6 (mod 16)
is excluded from the genuine accelerated blank-entry Reach predicate. -/
theorem blank_no_critical_6_mod16 (h : Nat) :
    ¬ BB6.Agent1.Reach 2 (14*2^(16*h+6)-2*(16*h+6)-10) := by
  let n := 16*h+6
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
  exact (six_no_hub h) (by simpa [n] using hhub)

#print axioms six_no_hub
#print axioms blank_no_critical_6_mod16
end BB6.Agent47P1
