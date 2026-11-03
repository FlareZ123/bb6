import Lean.Elab.Tactic.Omega
namespace BB6.Agent30Generic

def H (r c s z : Nat) : Nat := r*(z/2)+c+s*(z%2)
def iterH (r c s : Nat) : Nat → Nat → Nat
  | 0,z => z
  | n+1,z => iterH r c s n (H r c s z)

theorem H_even_shift (r c s z d : Nat) :
    H r c s (z+2*d)=H r c s z+r*d := by
  have hd : (z+2*d)/2=z/2+d := by omega
  have hp : (z+2*d)%2=z%2 := by omega
  simp only [H, hd, hp]
  simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem iterH_two_adic_shift (r c s n z d : Nat) :
    iterH r c s n (z+2^n*d)=iterH r c s n z+r^n*d := by
  induction n generalizing z d with
  | zero => simp [iterH]
  | succ n ih =>
    change iterH r c s n (H r c s (z+2^(n+1)*d)) =
      iterH r c s n (H r c s z) + r^(n+1)*d
    have hpow : 2^(n+1)*d = 2*(2^n*d) := by
      rw [Nat.pow_succ]
      ac_rfl
    rw [hpow,H_even_shift]
    have hin : H r c s z + r*(2^n*d) = H r c s z + 2^n*(r*d) := by
      ac_rfl
    rw [hin,ih]
    rw [Nat.pow_succ]
    ac_rfl

end BB6.Agent30Generic
