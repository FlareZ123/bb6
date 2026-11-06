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

/-- Every genuine inverse word below the wall retains the same
    strict logarithmic minimum cost as an exact-wall inverse word. -/
theorem word_subwall_logarithmic_gap
    {n K D m A T : Nat}
    (hn : 14 ≤ n) (hK : K+n+3=7*2^n)
    (hword : OddWord K D m A T)
    (hsub : K ≤ D+3*m+2*n+4) :
    2^(n-m) < n := by
  by_cases hm : n ≤ m
  · have hzero : n-m=0 := by omega
    simp only [hzero]
    simp
    omega
  · have hless : m < n := by omega
    let k := n-m
    have hnk : n = m+k := by dsimp [k]; omega
    have hP : 2^n = 2^m*2^k := by
      rw [hnk]
      exact Nat.pow_add 2 m k
    have hlin : n+4 ≤ 2^n := n_plus_four_le_pow n (by omega)
    have hcoeff : 3*m+2*n+4 ≤ 5*n+1 := by omega
    have hc := word_subwall_cost_necessary hword hsub
    have hbound : 7*2^n ≤ 2^n+2^m*(5*n+1) := by
      have hcoeffmul : 2^m*(3*m+2*n+4) ≤ 2^m*(5*n+1) :=
        Nat.mul_le_mul_left (2^m) hcoeff
      omega
    have hc6 : 6*2^n ≤ 2^m*(5*n+1) := by omega
    have hmult : 2^m*(6*2^k) ≤ 2^m*(5*n+1) := by
      calc
        _ = 6*2^n := by rw [hP]; ac_rfl
        _ ≤ _ := hc6
    have hpos : 0 < 2^m := Nat.pow_pos (by decide)
    have hkbound : 6*2^k ≤ 5*n+1 :=
      Nat.le_of_mul_le_mul_left hmult hpos
    have hkn : 2^k < n := by omega
    simpa only [show n-m=k by rfl] using hkn

/-- Original P1 critical OddCone, all depths, exact source transitions. -/
theorem source_critical_subwall_cost_logarithmic_gap
    (n b d m : Nat) (hn : 14 ≤ n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hb : b ≤ 4*(m+n)) : 2^(n-m) < n := by
  let K : Nat := 7*2^n-n-3
  have hdom : n+4 ≤ 2^n := n_plus_four_le_pow n (by omega)
  have hK : K+n+3=7*2^n := by dsimp [K]; omega
  have hroot : (14*2^n-2*n-16)+10=2*K := by
    dsimp [K]
    omega
  obtain ⟨D,A,T,hdD,hbalance,hword⟩ :=
    source_oddcone_has_word (14*2^n-2*n-16) K b d m hroot hcone
  have hsub : K ≤ D+3*m+2*n+4 := by omega
  exact word_subwall_logarithmic_gap hn hK hword hsub

#print axioms BB6.Agent50SubwallLog.word_subwall_cost_necessary
#print axioms BB6.Agent50SubwallLog.word_subwall_logarithmic_gap
#print axioms BB6.Agent50SubwallLog.source_critical_subwall_cost_logarithmic_gap

end BB6.Agent50SubwallLog
