import TwoShallowFiniteBounds
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43FiveLayer

/-- The exact two-profile table gives both a positive raw remainder and
the sharpened uniform upper bound needed by the five-layer peel. -/
theorem profile_time_bounds
  (t alpha C L O n T : Nat)
  (ht : t≤1)
  (hpr : (alpha,C,L,O)=BB6.Agent43TwoShallowFinite.triple t)
  (hTlo : n+6≤T)
  (hThi : T≤2*n+6) :
  1≤alpha ∧ 0<L*T-O ∧ L*T-O≤168*(n+2) := by
  cases t with
  | zero =>
      have hp : alpha=1 ∧ C=588 ∧ L=84 ∧ O=232 := by
        simpa [BB6.Agent43TwoShallowFinite.triple] using hpr
      rcases hp with ⟨rfl,rfl,rfl,rfl⟩
      constructor
      · omega
      constructor
      · have hprod : 84*(n+6)≤84*T := Nat.mul_le_mul_left 84 hTlo
        omega
      · have hprod : 84*T≤84*(2*n+6) := Nat.mul_le_mul_left 84 hThi
        omega
  | succ k =>
      have hk : k=0 := by omega
      subst k
      have hp : alpha=2 ∧ C=392 ∧ L=56 ∧ O=136 := by
        simpa [BB6.Agent43TwoShallowFinite.triple] using hpr
      rcases hp with ⟨rfl,rfl,rfl,rfl⟩
      constructor
      · omega
      constructor
      · have hprod : 56*(n+6)≤56*T := Nat.mul_le_mul_left 56 hTlo
        omega
      · have hprod : 56*T≤56*(2*n+6) := Nat.mul_le_mul_left 56 hThi
        omega

#print axioms profile_time_bounds

end BB6.Agent43FiveLayer
