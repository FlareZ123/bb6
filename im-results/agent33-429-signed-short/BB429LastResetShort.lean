import BB429RootShortSource

namespace BB429LastResetShort
open BB429NewResidue

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

/-- Conservative growth bound sufficient to ensure every genuine
    last-reset candidate with n>=18 has a large q index. -/
private theorem n_plus_500_le_power (n : Nat) (hn : 18 ≤ n) :
    n+500 ≤ 2^(n+2) := by
  induction hn with
  | refl => norm_num
  | @step n hn ih =>
    calc
      n+1+500 = n+500+1 := by omega
      _ ≤ 2^(n+2)+1 := by omega
      _ ≤ 2^(n+2)*2 := by omega
      _ = 2^(n+1+2) := by
        have hh : n+1+2 = (n+2)+1 := by omega
        rw [hh, Nat.pow_succ]

private theorem q_large (n q r : Nat)
    (hn : 18 ≤ n) (hr : r ≤ 15)
    (hreset : 4*(32*q+r)+3*n+15 = 3*2^(n+2)) :
    6 ≤ q := by
  have hp := n_plus_500_le_power n hn
  have hmul : 3*(n+500) ≤ 3*2^(n+2) :=
    Nat.mul_le_mul_left 3 hp
  omega

/-- Source-root impossibility on the 13-line q≡2 mod4,
    conditional only on the exact authentic final-reset arithmetic. -/
theorem no_source_13_q2 (n q : Nat)
    (hn : 18 ≤ n)
    (hreset : 4*(32*q+13)+3*n+15 = 3*2^(n+2))
    (hq : q%4=2) :
    ¬ Reach (32*q+13) (64*q+23) := by
  have hlarge : 6 ≤ q := q_large n q 13 hn (by omega) hreset
  let t := q/4
  have ht : 1 ≤ t := by dsimp [t]; omega
  have ha : 32*q+13 = 128*t+77 := by dsimp [t]; omega
  have hb : 64*q+23 = 256*t+151 := by dsimp [t]; omega
  rw [ha,hb]
  exact BB429RootShortSource.branch13_q2_unreachable t ht

theorem no_source_13_q3 (n q : Nat)
    (hn : 18 ≤ n)
    (hreset : 4*(32*q+13)+3*n+15 = 3*2^(n+2))
    (hq : q%4=3) :
    ¬ Reach (32*q+13) (64*q+23) := by
  have hlarge : 6 ≤ q := q_large n q 13 hn (by omega) hreset
  let t := q/4
  have ht : 1 ≤ t := by dsimp [t]; omega
  have ha : 32*q+13 = 128*t+109 := by dsimp [t]; omega
  have hb : 64*q+23 = 256*t+215 := by dsimp [t]; omega
  rw [ha,hb]
  exact BB429RootShortSource.branch13_q3_unreachable t ht

theorem no_source_15_q1 (n q : Nat)
    (hn : 18 ≤ n)
    (hreset : 4*(32*q+15)+3*n+15 = 3*2^(n+2))
    (hq : q%4=1) :
    ¬ Reach (32*q+15) (64*q+27) := by
  have hlarge : 6 ≤ q := q_large n q 15 hn (by omega) hreset
  let t := q/4
  have ht : 1 ≤ t := by dsimp [t]; omega
  have ha : 32*q+15 = 128*t+47 := by dsimp [t]; omega
  have hb : 64*q+27 = 256*t+91 := by dsimp [t]; omega
  rw [ha,hb]
  exact BB429RootShortSource.branch15_q1_unreachable t ht

private theorem power_div_four (n : Nat) (hn : 18 ≤ n) :
    4 ∣ 2^(n-5) := by
  have hp : 2^2 ∣ 2^(n-5) := Nat.pow_dvd_pow 2 (by omega)
  simpa using hp

/-- For the exact branch-13 last-reset parametrization
    q+3k+2=3·2^(n-5), *half* the possible k classes modulo four
    cannot be blank-root reachable. -/
theorem no_source_branch13_k0_or_k1
    (n k q : Nat) (hn : 18 ≤ n)
    (hreset : 4*(32*q+13)+3*n+15 = 3*2^(n+2))
    (hparam : q+(3*k+2) = 3*2^(n-5))
    (hk : k%4=0 ∨ k%4=1) :
    ¬ Reach (32*q+13) (64*q+23) := by
  have hpow : (2^(n-5))%4=0 :=
    Nat.mod_eq_zero_of_dvd (power_div_four n hn)
  rcases hk with hk0 | hk1
  · have hq : q%4=2 := by omega
    exact no_source_13_q2 n q hn hreset hq
  · have hq : q%4=3 := by omega
    exact no_source_13_q3 n q hn hreset hq

theorem no_source_branch15_k0
    (n k q : Nat) (hn : 18 ≤ n)
    (hreset : 4*(32*q+15)+3*n+15 = 3*2^(n+2))
    (hparam : q+(3*k+3) = 3*2^(n-5))
    (hk : k%4=0) :
    ¬ Reach (32*q+15) (64*q+27) := by
  have hpow : (2^(n-5))%4=0 :=
    Nat.mod_eq_zero_of_dvd (power_div_four n hn)
  have hq : q%4=1 := by omega
  exact no_source_15_q1 n q hn hreset hq

#print axioms no_source_branch13_k0_or_k1
#print axioms no_source_branch15_k0
end BB429LastResetShort
