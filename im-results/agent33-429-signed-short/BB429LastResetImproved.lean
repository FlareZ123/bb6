import BB429Forced13More
import BB429Forced15

namespace BB429LastResetImproved
open BB429NewResidue

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

/-- A coarse, uniform exponential inequality, needed only to keep each
    last-reset q above all original positive-output inverse thresholds. -/
private theorem n_plus_1000_le_power (n : Nat) (hn : 18 ≤ n) :
    n+1000 ≤ 2^(n+2) := by
  induction hn with
  | refl => norm_num
  | @step n hn ih =>
    calc
      n+1+1000 = n+1000+1 := by omega
      _ ≤ 2^(n+2)+1 := by omega
      _ ≤ 2^(n+2)*2 := by omega
      _ = 2^(n+1+2) := by
        have heq : n+1+2=(n+2)+1 := by omega
        rw [heq, Nat.pow_succ]

/-- Any authentic branch-7 last-reset arithmetic solution with n>=18
    has q>=16, far beyond the finite special-output region. -/
theorem genuine_last_reset_q_large (n q r : Nat)
    (hn : 18 ≤ n) (hr : r ≤ 15)
    (hreset : 4*(32*q+r)+3*n+15 = 3*2^(n+2)) :
    16 ≤ q := by
  have he := n_plus_1000_le_power n hn
  have hh : 3*(n+1000) ≤ 3*2^(n+2) :=
    Nat.mul_le_mul_left 3 he
  omega

private theorem power_mod16_zero (n : Nat) (hn : 18 ≤ n) :
    2^(n-5)%16=0 := by
  have hd : 2^4 ∣ 2^(n-5) := Nat.pow_dvd_pow 2 (by omega)
  have h16 : 16 ∣ 2^(n-5) := by simpa using hd
  exact Nat.mod_eq_zero_of_dvd h16

/-- Original blank-source branch-13 final-reset equation leaves only
    k=6,11,14(mod16), rather than all sixteen congruence classes.
    Uses the uniform 8-inverse source theorem, not finite enumeration. -/
theorem source_branch13_k_mod16_necessary
    (n k q : Nat) (hn : 18 ≤ n)
    (hreset : 4*(32*q+13)+3*n+15 = 3*2^(n+2))
    (hparam : q+(3*k+2) = 3*2^(n-5))
    (hr : Reach (32*q+13) (64*q+23)) :
    k%16=6 ∨ k%16=11 ∨ k%16=14 := by
  have hq : 16≤q :=
    genuine_last_reset_q_large n q 13 hn (by omega) hreset
  have hclass := BB429Forced13More.rooted_13_q_mod16 q hq hr
  have hp := power_mod16_zero n hn
  omega

/-- Original blank-source branch-15 final-reset equation excludes
    the entire k=0(mod4) parameter class (not merely finite k). -/
theorem source_branch15_k_not0_mod4
    (n k q : Nat) (hn : 18 ≤ n)
    (hreset : 4*(32*q+15)+3*n+15 = 3*2^(n+2))
    (hparam : q+(3*k+3) = 3*2^(n-5))
    (hr : Reach (32*q+15) (64*q+27)) :
    k%4≠0 := by
  intro hk
  have hq : 16≤q :=
    genuine_last_reset_q_large n q 15 hn (by omega) hreset
  have hp := power_mod16_zero n hn
  have hqm : q%4=1 := by omega
  let t := q/4
  have ht : 1≤t := by dsimp [t]; omega
  have ha : 32*q+15=128*t+47 := by dsimp [t]; omega
  have hb : 64*q+27=256*t+91 := by dsimp [t]; omega
  rw [ha,hb] at hr
  exact BB429Forced15.rooted_15_q1_mod4_excluded t ht hr

#print axioms genuine_last_reset_q_large
#print axioms source_branch13_k_mod16_necessary
#print axioms source_branch15_k_not0_mod4
end BB429LastResetImproved
