import Lean
namespace CascadeSeam

private theorem two_pow_residue (n : Nat) : (2^n)%3 = 1 ∨ (2^n)%3 = 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    rcases ih with h|h <;> simp [h]

private theorem three_pow_residue (n : Nat) (hn : 0<n) : (3^n)%3 = 0 := by
  cases n with
  | zero => omega
  | succ n => rw [Nat.pow_succ,Nat.mul_mod]; simp

private theorem mul_two_pow_unit (n p : Nat) (hp : p%3 ≠ 0) : (2^n*p)%3 ≠ 0 := by
  have hr : p%3=1 ∨ p%3=2 := by omega
  rw [Nat.mul_mod]
  rcases two_pow_residue n with h|h <;> rcases hr with hp'|hp' <;> simp [h,hp']

/-- The odd branch's integrality forces divisibility of its target by 3 in
    the coordinate 2u+5. -/
theorem odd_target_mod3 (a u S : Nat) (ha : 0<a)
    (he : 2^a*(2*u+5)=3^a*S) : (2*u+5)%3=0 := by
  by_cases hn : (2*u+5)%3=0
  · exact hn
  · exfalso
    have hc := mul_two_pow_unit a (2*u+5) hn
    rw [he,Nat.mul_mod,three_pow_residue a ha] at hc
    simp at hc

/-- At a canonical spine departure, the initial scaled ideal numerator is
    a unit modulo 3, since 2K+5 is a unit. -/
theorem spine_departure_unit (u K P : Nat) (hp : u=K+P)
    (hu : (2*u+5)%3=0) (hk : (2*K+5)%3 ≠ 0) : P%3 ≠ 0 := by
  omega

/-- Scaled ideal inverse recurrence, P = 3^A * 2^K * z. Once an odd edge
    has been taken, its numerator remains a 3-adic unit. -/
theorem ideal_numerator_unit (P Q a A k : Nat)
    (hA : 0<A+a) (hP : P%3 ≠ 0)
    (he : Q+8*2^k*3^(A+a)=2^(a+1)*P) : Q%3 ≠ 0 := by
  have hm := congrArg (fun n : Nat => n%3) he
  rw [Nat.add_mod, Nat.mul_mod (8*2^k), three_pow_residue (A+a) hA] at hm
  simp at hm
  rw [hm]
  exact mul_two_pow_unit (a+1) P hP

/-- A genuine post-odd ideal value cannot be any dyadic rational, even if
    the ideal path began at a late point of the canonical ray. -/
theorem no_dyadic_ideal (P A k b num : Nat) (hA : 0<A)
    (hP : P%3 ≠ 0) : P*2^b ≠ num*(3^A*2^k) := by
  intro he
  have hn := mul_two_pow_unit b P hP
  rw [Nat.mul_comm] at hn
  rw [he,Nat.mul_mod num,Nat.mul_mod (3^A),three_pow_residue A hA] at hn
  simp at hn

/-- The initial odd departure's source level K=N-1 has the required unit
    for both surviving fatal sectors. -/
theorem surviving_level_unit (N K : Nat) (hk : N=K+1)
    (hs : N%6=4 ∨ N%6=5) : (2*K+5)%3 ≠ 0 := by
  omega

#print axioms odd_target_mod3
#print axioms spine_departure_unit
#print axioms ideal_numerator_unit
#print axioms no_dyadic_ideal
#print axioms surviving_level_unit
end CascadeSeam
