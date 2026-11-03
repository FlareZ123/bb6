import Lean.Elab.Tactic.Omega

namespace BB6.GeneralParity

def H (a b c z : Nat) : Nat := (a*z + b + c*(z%2))/2

theorem H_even_shift (a b c z t : Nat) :
    H a b c (z+2*t) = H a b c z + a*t := by
  have hparity : (z+2*t)%2=z%2 := by omega
  simp only [H, hparity]
  have hx : a*(z+2*t)+b+c*(z%2) = (a*z+b+c*(z%2)) + 2*(a*t) := by
    rw [Nat.mul_add]
    have ht : a*(2*t)=2*(a*t) := by ac_rfl
    rw [ht]
    omega
  rw [hx]
  omega

theorem H_odd_increment (a b c z t : Nat)
    (ha : a%2=1) (hb : b%2=0) (hc : c%2=1) (ht : t%2=1) :
    2*H a b c (z+t) = 2*H a b c z + a*t + c ∨
    2*H a b c (z+t) + c = 2*H a b c z + a*t := by
  have parity_num (x : Nat) : (a*x+b+c*(x%2))%2=0 := by
    have hh : (a*x)%2=x%2 := by rw [Nat.mul_mod,ha]; omega
    have hc2 : (c*(x%2))%2=x%2 := by rw [Nat.mul_mod,hc]; omega
    omega
  have twice (x : Nat) : 2*H a b c x = a*x+b+c*(x%2) := by
    have h := parity_num x
    simp only [H]
    omega
  have h0 := twice z
  have h1 := twice (z+t)
  have hm : a*(z+t) = a*z+a*t := Nat.mul_add ..
  rw [hm] at h1
  rcases (show z%2=0 ∨ z%2=1 by omega) with he | ho
  · left
    have hp : (z+t)%2=1 := by omega
    rw [he] at h0
    rw [hp] at h1
    omega
  · right
    have hp : (z+t)%2=0 := by omega
    rw [ho] at h0
    rw [hp] at h1
    omega

end BB6.GeneralParity
