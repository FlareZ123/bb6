import FullReturn

namespace CascadeResetInverse

/-- Exact inverse height equation and dyadic image band for even first return. -/
theorem even_inverse_band (h k : Nat)
  (hlow : 4*2^k≤h+k+4)
  (hhigh : h+k+5<8*2^k)
  (hnot : h+k+4≠4*2^k)
  (hpar : (h+k)%2=0) :
  let u := 4*2^k+(h+k)/2
  (6*2^k-1≤u ∧ u≤8*2^k-3) ∧
    2*u=8*2^k+h+k := by
  dsimp
  have hq : h+k=2*((h+k)/2) := by omega
  constructor
  · constructor <;> omega
  · omega

/-- Exact odd-phase initial q band and source predecessor equation. -/
theorem odd_inverse_band (h k : Nat)
  (hlow : 4*2^k≤h+k+4)
  (hhigh : h+k+5<8*2^k)
  (hnot : h+k+4≠4*2^k)
  (hpar : (h+k)%2=1) :
  let q := 4*2^k+(h+k)/2+3
  (6*2^k+1≤q ∧ q≤8*2^k-1) ∧
    2*q=8*2^k+h+k+5 := by
  dsimp
  have hq : h+k=2*((h+k)/2)+1 := by omega
  constructor
  · constructor <;> omega
  · omega

private theorem three_pow_odd (n : Nat) : (3^n)%2=1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hs : 3^(n+1)=3^n*3 := by rw [Nat.pow_succ]
    rw [hs,Nat.mul_mod,ih]

/-- The valuation drain's output is odd-cubic as an integer, with no hidden
    truncation in division by two, for every genuine q>=7 input. -/
theorem odd_output_equation (t d : Nat) (hd : d%2=1)
  (hq : 7≤2^t*d) :
  2*((3^(t+1)*d-5)/2)+5 = 3^(t+1)*d := by
  have hp := three_pow_odd (t+1)
  have hm : (3^(t+1)*d)%2=1 := by
    simp [Nat.mul_mod,hp,hd]
  have hcomp : ∀t, 2^t≤3^(t+1) := by
    intro t
    induction t with
    | zero => decide
    | succ t ih =>
      have h2 : 2^(t+1)=2*2^t := by rw [Nat.pow_succ]; omega
      have h3 : 3^((t+1)+1)=3*(3^(t+1)) := by rw [Nat.pow_succ];omega
      rw [h2,h3]
      omega
  have hmul := Nat.mul_le_mul_right d (hcomp t)
  have hbig : 5≤3^(t+1)*d := by omega
  omega

#print axioms even_inverse_band
#print axioms odd_inverse_band
#print axioms odd_output_equation
end CascadeResetInverse
