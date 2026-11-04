import Orbit192Proof
import Lean.Elab.Tactic.Omega

namespace CQuotient192

private theorem power_mod192 (n : Nat) : 2 ^ (2*(n+3)+3) % 192 = 128 := by
  induction n with
  | zero => decide
  | succ n ih =>
      have he : 2*((n+1)+3)+3 = (2*(n+3)+3)+2 := by omega
      rw [he, Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

theorem first_m58_if_closed
    (hc : ∀ p : Fin 5, ∀ x y : Fin 192,
      closedAt p.val x.val y.val = true)
    (m k : Nat) (hm : m % 64 = 58)
    (hk : k+3*m+4 = 2^(2*m+3)) :
    ¬ BB6CLine.Reach (1,k,0) := by
  have hmge : 3 ≤ m := by omega
  have hpow : 2^(2*m+3)%192=128 := by
    have hh := power_mod192 (m-3)
    have he : 2*((m-3)+3)+3 = 2*m+3 := by omega
    simpa only [he] using hh
  have hkmod : k%192=142 := by
    have hh : (k+3*m+4)%192=128 := by rw [hk]; exact hpow
    omega
  exact no_142_if_closed hc k hkmod

#print axioms first_m58_if_closed
end CQuotient192
