import Lean
import Lean.Elab.Tactic.Omega

/-!
F321 inverse-word arithmetic kernel.
A bounded-depth modular exclusion result needs a word of high/far
inverse moves to carry an *odd* coefficient of the unknown terminal d.
This module proves the coefficient-parity invariant and the exact
counter-sum decrements over arbitrary integral inverse transitions.
It does NOT prove the original-machine counter reduction, the
density theorem, or unbounded F321 nonhalting.
-/

namespace BB6.Agent31F321Density

inductive InverseLetter where
  | high
  | far
  deriving DecidableEq, Repr

structure ArithmeticCert where
  u : Nat
  v : Int
  shift : Nat
  sumDecrease : Nat
  deriving Repr

def initial : ArithmeticCert :=
  {u := 1, v := 1, shift := 0, sumDecrease := 0}

def advance (z : ArithmeticCert) : InverseLetter → ArithmeticCert
  | .high => {
      u := z.u + 2^(z.shift+1),
      v := z.v + (2:Int)^z.shift * (2-(z.sumDecrease:Int)),
      shift := z.shift+1,
      sumDecrease := z.sumDecrease+1 }
  | .far => {
      u := z.u,
      v := z.v - 6*(2:Int)^z.shift,
      shift := z.shift+2,
      sumDecrease := z.sumDecrease+6 }

def compile : List InverseLetter → ArithmeticCert
  | [] => initial
  | b :: bs => advance (compile bs) b

private theorem pow_two_succ_even (n : Nat) :
    (2^(n+1) : Nat) % 2 = 0 := by
  rw [Nat.pow_succ]
  omega

theorem advance_preserves_odd (z : ArithmeticCert) (b : InverseLetter)
    (h : z.u % 2 = 1) : (advance z b).u % 2 = 1 := by
  cases b with
  | high =>
      have heven := pow_two_succ_even z.shift
      simp only [advance]
      omega
  | far =>
      simpa [advance] using h

/-- A formal word has an odd coefficient of terminal parameter d;
    hence it has at most one admissible residue modulo 2^shift. -/
theorem compiled_numerator_odd (w : List InverseLetter) :
    (compile w).u % 2 = 1 := by
  induction w with
  | nil => rfl
  | cons b bs ih => exact advance_preserves_odd (compile bs) b ih

/-- Every genuine inverse high step reduces counter sum by exactly one. -/
theorem high_inverse_sum
    {A D A' D' : Int}
    (hA : 2*A' = 2*A+D+1)
    (hD : 2*D' = D-3) :
    A'+D' = A+D-1 := by
  omega

/-- Every genuine inverse far step reduces counter sum by exactly six. -/
theorem far_inverse_sum
    {A D A' D' : Int}
    (hA : 4*A' = A-6)
    (hD : D' = D+3*A') :
    A'+D' = A+D-6 := by
  omega

/-- The high inverse decreases the second coordinate according to the
    exact source equation, with no asymptotic approximation. -/
theorem high_second_barrier
    {D D' B : Int}
    (hD : 2*D' = D-3)
    (hB : B ≤ D) :
    2*(D'+3) ≥ B+3 := by
  omega

/-- The far inverse is monotone nondecreasing on the second coordinate
    whenever its guard A≥6 holds. -/
theorem far_second_monotone
    {A D D' : Int}
    (hA : 6 ≤ A)
    (hD : 4*D' = 4*D + 3*(A-6)) :
    D ≤ D' := by
  omega

#print axioms compiled_numerator_odd
#print axioms high_inverse_sum
#print axioms far_inverse_sum
#print axioms high_second_barrier
#print axioms far_second_monotone

end BB6.Agent31F321Density
