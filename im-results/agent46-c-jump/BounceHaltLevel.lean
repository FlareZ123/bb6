import BounceParity
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- High counter level that halts after n complete even-middle bounces. -/
def haltLevel (k : Nat) : Nat → Nat
  | 0 => 5
  | n+1 => 2*k+5 + haltLevel (2*k+4) n

theorem haltLevel_ge_five (k n : Nat) : 5≤haltLevel k n := by
  cases n with
  | zero => simp [haltLevel]
  | succ n =>
      simp only [haltLevel]
      have h := haltLevel_ge_five (2*k+4) n
      omega

theorem even_halt_bounce (n : Nat) : ∀ k, k%2=0 →
    (bounce k (haltLevel k n)).2=none := by
  induction n with
  | zero =>
    intro k hk
    rw [haltLevel,bounce.eq_1]
    simp [hk]
  | succ n ih =>
    intro k hk
    let t := haltLevel (2*k+4) n
    have ht : 5≤t := haltLevel_ge_five _ _
    have hc : haltLevel k (n+1) = 2*k+5+t := rfl
    have hlarge : 2*k+8<haltLevel k (n+1) := by omega
    have hnot : ¬haltLevel k (n+1)<4 := by omega
    have hc4 : haltLevel k (n+1)≠4 := by omega
    have hc5 : haltLevel k (n+1)≠5 := by omega
    have hmid : (haltLevel k (n+1))-(2*k+5)=t := by omega
    rw [bounce.eq_1]
    simp only [hnot,ite_false,hk,hc4,hc5,
      show ¬haltLevel k (n+1)≤2*k+8 by omega, hmid]
    exact ih (2*k+4) (by omega)

#print axioms even_halt_bounce
end BB6.Agent46
