import OddWordSourceBridge

namespace BB6.Agent50SubwallLog
open BB6.Agent28 BB6.Agent1Quarter

/-- Binary-word cost obstruction for a lower-or-equal-left endpoint. -/
theorem word_subwall_cost_necessary
    {K D m A T n : Nat}
    (hword : OddWord K D m A T)
    (hsub : K ≤ D+3*m+2*n+4) :
    K ≤ 1+2^m*(3*m+2*n+4) := by
  have hsmall := hword.binary_coefficient_small
  have hmass := hword.mass_identity
  have hAle : A+1 ≤ 2^m := by omega
  have hmul : K*(A+1) ≤ K*2^m := Nat.mul_le_mul_left K hAle
  have hpow :
      2^m*K+T ≤ (1+K*A)+2^m*(3*m+2*n+4) := by
    calc
      2^m*K+T ≤ 2^m*(D+3*m+2*n+4)+T := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left (2^m) hsub) T
      _ = (2^m*D+T)+2^m*(3*m+2*n+4) := by
        simp only [Nat.mul_add]; ac_rfl
      _ = (1+K*A)+2^m*(3*m+2*n+4) := by rw [hmass]
  have hrewrite : K*(A+1) = K*A+K := by
    simp only [Nat.mul_add]
    omega
  have hAlimit : K*A+K ≤ 2^m*K := by
    rw [← hrewrite]
    simpa only [Nat.mul_comm K (2^m)] using hmul
  omega

private theorem n_plus_four_le_pow (n : Nat) (hn : 4 ≤ n) : n+4 ≤ 2^n := by
  have hb : ∀ t : Nat, (t+4)+4 ≤ 2^(t+4) := by
    intro t
    induction t with
    | zero => decide
    | succ t ih =>
      have hidx : (t+1)+4 = (t+4)+1 := by omega
      rw [hidx, Nat.pow_succ]
      omega
  have heq : (n-4)+4 = n := by omega
  simpa only [heq] using hb (n-4)

end BB6.Agent50SubwallLog
