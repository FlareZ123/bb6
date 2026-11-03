import FirstM11
import Lean.Elab.Tactic.Omega

namespace B192

private theorem power_mod192 (n : Nat) : 2 ^ (2*(n+3)+3) % 192 = 128 := by
  induction n with
  | zero => decide
  | succ n ih =>
      have he : 2*((n+1)+3)+3 = (2*(n+3)+3)+2 := by omega
      rw [he, Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- The entire first-stopping parameter residue m=11 modulo64 is impossible
    for the genuine blank accelerated Machine C source orbit. -/
theorem first_halt_m11_mod64_unreachable (m k : Nat)
    (hm : m % 64 = 11)
    (hk : k + 3*m + 4 = 2 ^ (2*m+3)) :
    ¬ BB6CLine.Reach (1,k,0) := by
  have hmge : 3 ≤ m := by omega
  have hpow : 2 ^ (2*m+3) % 192 = 128 := by
    have hform : 2*((m-3)+3)+3 = 2*m+3 := by omega
    simpa only [hform] using power_mod192 (m-3)
  have hkmod : k % 192 = 91 := by
    have he : (k+3*m+4)%192=128 := by rw [hk]; exact hpow
    omega
  exact first_91_mod192_unreachable k hkmod

#print axioms B192.first_halt_m11_mod64_unreachable
end B192
