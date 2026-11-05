import Lean
namespace BB6.Shadow

/-- At a safely encoded shadow hub the low t+2 bits of the shifted
right counter are determined by twice the shadow coordinate z. -/
theorem encoded_shift_divisible
    (N L m t b d w z alpha : Nat)
    (hmass : b+d+2*m+2*L+3 = 56*2^N)
    (hoff : L+m = w+z)
    (henc : b+4*w = alpha*2^(N-m))
    (hbeven : b%2=0)
    (hsafe : m+t+3 ≤ N) :
    2^(t+2) ∣ d+b/2+3+2*z := by
  have hn0 : m+1 ≤ N := by omega
  have hnpow : 2^(N-m) = 2*2^(N-m-1) := by
    have heq : N-m=(N-m-1)+1 := by omega
    calc
      2^(N-m) = 2^((N-m-1)+1) := congrArg (fun k : Nat => 2^k) heq
      _ = 2^(N-m-1)*2 := by rw [Nat.pow_succ]
      _ = 2*2^(N-m-1) := by omega
  have hbhalf : b=2*(b/2) := by omega
  have hexact : (d+b/2+3+2*z) + alpha*2^(N-m-1) = 56*2^N := by
    have henc2 : b+4*w = 2*(alpha*2^(N-m-1)) := by
      calc
        b+4*w = alpha*2^(N-m) := henc
        _ = 2*(alpha*2^(N-m-1)) := by rw [hnpow]; simp [Nat.mul_left_comm]
    omega
  have hh : 2^(t+2) ∣ 2^(N-m-1) := Nat.pow_dvd_pow 2 (by omega)
  have hhN : 2^(t+2) ∣ 2^N := Nat.pow_dvd_pow 2 (by omega)
  have hhl : 2^(t+2) ∣ alpha*2^(N-m-1) := by
    obtain ⟨r,hr⟩ := hh
    refine ⟨alpha*r, ?_⟩
    rw [hr]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hhr : 2^(t+2) ∣ 56*2^N := by
    obtain ⟨r,hr⟩ := hhN
    refine ⟨56*r, ?_⟩
    rw [hr]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hdiff : 2^(t+2) ∣ 56*2^N-alpha*2^(N-m-1) := Nat.dvd_sub hhr hhl
  have heq : d+b/2+3+2*z=56*2^N-alpha*2^(N-m-1) := by omega
  rw [heq]
  exact hdiff

/-- Odd inverse output at depth t forces t binary factors in shadow z. -/
theorem odd_inverse_divisible (t Q c z s : Nat)
    (h : s + 2*z = 2^(t+2)*Q)
    (h2 : s = 2^t*(c+3))
    (hc : c%2=1) : 2^t ∣ z := by
  let a := 2^t
  let u := c/2+2
  have he : c+3 = 2*u := by dsimp [u]; omega
  have hp : 2^(t+2) = 4*a := by
    simp [a, Nat.pow_add, Nat.mul_comm]
  have hh : 2*(z+a*u) = 2*(a*(2*Q)) := by
    calc
      2*(z+a*u) = a*(2*u)+2*z := by grind
      _ = s+2*z := by rw [h2, he]
      _ = 2^(t+2)*Q := h
      _ = 2*(a*(2*Q)) := by rw [hp]; grind
  have heq : z+a*u = a*(2*Q) := Nat.mul_left_cancel (by decide : 0 < (2:Nat)) hh
  have hdiv : a ∣ a*(2*Q)-a*u := Nat.dvd_sub (Nat.dvd_mul_right a (2*Q)) (Nat.dvd_mul_right a u)
  have hz : z = a*(2*Q)-a*u := by omega
  rw [hz]
  exact hdiv

#print axioms encoded_shift_divisible
#print axioms odd_inverse_divisible
end BB6.Shadow
