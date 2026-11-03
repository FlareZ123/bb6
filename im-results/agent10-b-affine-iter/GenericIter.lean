import GenericMap
namespace BB6.GeneralParity

def Iter (a b c : Nat) : Nat → Nat → Nat
  | 0, z => z
  | n+1, z => H a b c (Iter a b c n z)

theorem iter_shift (a b c n z d : Nat) :
    Iter a b c n (z+2^n*d) = Iter a b c n z + a^n*d := by
  induction n generalizing z d with
  | zero => simp [Iter]
  | succ n ih =>
    change H a b c (Iter a b c n (z+2^(n+1)*d)) =
      H a b c (Iter a b c n z)+a^(n+1)*d
    have he : 2^(n+1)*d=2^n*(2*d) := by
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    rw [he, ih]
    have hm : a^n*(2*d)=2*(a^n*d) := by ac_rfl
    rw [hm,H_even_shift]
    simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
end BB6.GeneralParity
