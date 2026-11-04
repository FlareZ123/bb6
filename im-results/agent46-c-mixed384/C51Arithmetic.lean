import C51
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace BB6.Agent46C51

private theorem pow4_mod3 (m : Nat) : 4^m % 3 = 1 := by
  induction m with
  | zero => decide
  | succ m ih =>
      rw [Nat.pow_succ]
      omega

private theorem low_pow_mod384 (m : Nat) (hm : 2≤m) :
    2^(2*m+3)%384 = 128 := by
  have hp : 2^(2*m+3)=128*4^(m-2) := by
    have he : 2*m+3 = 7+2*(m-2) := by omega
    rw [he,Nat.pow_add]
    have ha : 2^(2*(m-2)) = 4^(m-2) := by
      calc
        2^(2*(m-2)) = (2^2)^(m-2) := Nat.pow_mul 2 2 (m-2)
        _ = 4^(m-2) := by simp
    rw [ha]
  rw [hp]
  have ht := pow4_mod3 (m-2)
  omega

theorem first_halt_m51_mod128_unreachable (m k : Nat)
    (hm : m%128=51)
    (hgate : k+3*m+4=2^(2*m+3)) :
    ¬ BB6CLine.Reach (1,k,0) := by
  have hp := low_pow_mod384 m (by omega)
  have hk : k%384=355 := by
    rw [←hgate] at hp
    omega
  exact first_355_mod384_unreachable k hk

#print axioms first_halt_m51_mod128_unreachable
end BB6.Agent46C51
