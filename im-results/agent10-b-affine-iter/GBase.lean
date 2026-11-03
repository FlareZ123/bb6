import Lean.Elab.Tactic.Omega

namespace BB6.Agent10IterBarrier

def G (z : Nat) : Nat := 3*(z/2)+4+5*(z%2)

def F : Nat → Nat → Nat
 | 0,z => z
 | n+1,z => G (F n z)

theorem two_G (z : Nat) : 2*G z = 3*z+8+7*(z%2) := by
  simp only [G]
  omega

theorem G_even_shift (z d : Nat) : G (z+2*d) = G z+3*d := by
  have h := two_G (z+2*d)
  have hz := two_G z
  have hp : (z+2*d)%2 = z%2 := by omega
  rw [hp] at h
  omega

theorem F_shift (n z d : Nat) : F n (z+2^n*d) = F n z+3^n*d := by
  induction n generalizing z d with
  | zero => simp [F]
  | succ n ih =>
    change G (F n (z+2^(n+1)*d)) = G (F n z)+3^(n+1)*d
    have he : 2^(n+1)*d=2^n*(2*d) := by
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    rw [he, ih]
    have hm : 3^n*(2*d) = 2*(3^n*d) := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    rw [hm, G_even_shift]
    simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem G_midpoint (z t : Nat) (ht : t%2=1) :
  G z + G (z+2*t)+7=2*G (z+t) ∨
  G z + G (z+2*t)=2*G (z+t)+7 := by
  have h0:=two_G z
  have h1:=two_G (z+t)
  have h2:=two_G (z+2*t)
  have hp0 : z%2=0 ∨ z%2=1 := by omega
  rcases hp0 with he | ho
  · left
    have hm : (z+t)%2=1 := by omega
    have hp : (z+2*t)%2=0 := by omega
    rw [he] at h0
    rw [hm] at h1
    rw [hp] at h2
    omega
  · right
    have hm : (z+t)%2=0 := by omega
    have hp : (z+2*t)%2=1 := by omega
    rw [ho] at h0
    rw [hm] at h1
    rw [hp] at h2
    omega
end BB6.Agent10IterBarrier
