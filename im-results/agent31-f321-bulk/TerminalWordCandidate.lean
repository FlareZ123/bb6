import DensityOneExtension
import Lean.Elab.Tactic.Omega

/-!
Exact terminal-parameter extraction from an F321 formal inverse H/F word.

For a terminal-seeded formal inverse path ending at '(R,c)', the word itself
fixes a positive denominator. Combined with the exact scaled-first-coordinate
and counter-sum certificates, this gives one Diophantine equation for the
terminal parameter. Thus a fixed word and anchor second counter can describe
at most one terminal parameter.
-/

namespace BB6.Agent31F321Density

/-- Positive complement of the odd numerator coefficient inside the next
    dyadic power. High leaves it fixed; Far adds a positive dyadic multiple
    of three. -/
def terminalDenom : List InverseLetter → Nat
  | [] => 1
  | .high :: w => terminalDenom w
  | .far :: w => terminalDenom w + 3 * 2^((compile w).shift+1)

/-- The recursive denominator is exactly '2^(shift+1) - u', expressed without
    truncated subtraction. -/
theorem terminalDenom_identity (w : List InverseLetter) :
    (compile w).u + terminalDenom w = 2^((compile w).shift+1) := by
  induction w with
  | nil => rfl
  | cons b bs ih =>
      cases b with
      | high =>
          simp [compile, advance, terminalDenom] at ih ⊢
          have hp : 2 ^ ((compile bs).shift + 1 + 1) =
              2 * 2 ^ ((compile bs).shift + 1) := by
            rw [Nat.pow_succ]
            exact Nat.mul_comm _ _
          omega
      | far =>
          simp [compile, advance, terminalDenom] at ih ⊢
          have hp : 2 ^ ((compile bs).shift + 2 + 1) =
              4 * 2 ^ ((compile bs).shift + 1) := by
            rw [show (compile bs).shift + 2 + 1 =
                ((compile bs).shift + 1) + 2 by omega]
            rw [Nat.pow_add]
            have h22 : (2:Nat)^2 = 4 := by decide
            rw [h22]
            exact Nat.mul_comm _ _
          omega

theorem terminalDenom_pos (w : List InverseLetter) : 0 < terminalDenom w := by
  induction w with
  | nil => decide
  | cons b bs ih =>
      cases b <;> simp [terminalDenom] <;> omega

/-- Every word denominator lies in the single congruence class 1 mod 6. -/
theorem terminalDenom_mod6 (w : List InverseLetter) :
    terminalDenom w % 6 = 1 := by
  induction w with
  | nil => decide
  | cons b bs ih =>
      cases b with
      | high => simpa [terminalDenom] using ih
      | far =>
          simp [terminalDenom]
          have hp : 2 ∣ 2^((compile bs).shift+1) := by
            refine ⟨2^(compile bs).shift, ?_⟩
            rw [Nat.pow_succ]
            exact Nat.mul_comm _ _
          rcases hp with ⟨k,hk⟩
          rw [hk]
          omega

/-- Exact signed right side of the terminal-candidate equation. -/
def terminalNumerator (c : Nat) (w : List InverseLetter) : Int :=
    (compile w).v + (2:Int)^(compile w).shift *
      ((compile w).sumDecrease + (c:Int) - 1)

private theorem eliminate_anchor
    (P u q v S d R c : Int)
    (hq : q + u = 2*P)
    (hscaled : P*R = u*d + v)
    (hsum : R+c = 2*d+1-S) :
    q*d = v + P*(S+c-1) := by
  have hqd := congrArg (fun z : Int => z*d) hq
  have hsp := congrArg (fun z : Int => P*z) hsum
  simp only [Int.add_mul, Int.mul_add, Int.mul_sub] at hqd hsp
  have h2pd : (2*P)*d = 2*(P*d) := by ac_rfl
  have hP2d : P*(2*d) = 2*(P*d) := by ac_rfl
  rw [h2pd] at hqd
  rw [hP2d] at hsp
  have hPS : P*(S+c-1) = P*S + P*c - P := by
    simp only [Int.mul_sub, Int.mul_add, Int.mul_one]
  rw [hPS]
  omega

/-- A genuine terminal-seeded formal inverse path to '(R,c)' forces one exact
    word-indexed equation for the terminal parameter 'd'. -/
theorem formal_inverse_terminal_candidate
    {d R c : Nat} {w : List InverseLetter}
    (hp : FormalInversePath (d:Int) w (R:Int) (c:Int)) :
    (terminalDenom w : Int) * (d:Int) = terminalNumerator c w := by
  have hc := formal_inverse_path_certificate hp
  have hscaled := hc.1
  have hsum := hc.2
  unfold scaledA at hscaled
  unfold sumAt at hsum
  unfold terminalNumerator
  have hdenNat := terminalDenom_identity w
  have hden := congrArg (fun z : Nat => (z:Int)) hdenNat
  rw [Int.natCast_add, Int.natCast_pow] at hden
  change ((compile w).u:Int) + (terminalDenom w:Int) =
      (2:Int)^((compile w).shift+1) at hden
  have hp2 : (2:Int)^((compile w).shift+1) =
      2 * (2:Int)^(compile w).shift := by
    rw [Int.pow_succ]
    ac_rfl
  rw [hp2] at hden
  exact eliminate_anchor
    ((2:Int)^(compile w).shift)
    ((compile w).u:Int)
    (terminalDenom w:Int)
    (compile w).v
    ((compile w).sumDecrease:Int)
    (d:Int) (R:Int) (c:Int)
    (by omega) hscaled hsum

/-- For fixed inverse word and fixed small-second anchor class, the terminal
    parameter is unique. -/
theorem formal_inverse_terminal_unique
    {d₁ d₂ R₁ R₂ c : Nat} {w : List InverseLetter}
    (h₁ : FormalInversePath (d₁:Int) w (R₁:Int) (c:Int))
    (h₂ : FormalInversePath (d₂:Int) w (R₂:Int) (c:Int)) :
    d₁ = d₂ := by
  have e₁ := formal_inverse_terminal_candidate h₁
  have e₂ := formal_inverse_terminal_candidate h₂
  have hq := terminalDenom_pos w
  have hqz : (0:Int) < (terminalDenom w:Int) := by exact_mod_cast hq
  have hmul : (terminalDenom w:Int) * (d₁:Int) =
      (terminalDenom w:Int) * (d₂:Int) := by
    rw [e₁, e₂]
  have hqne : (terminalDenom w:Int) ≠ 0 := by omega
  have hd : (d₁:Int) = (d₂:Int) :=
    Int.eq_of_mul_eq_mul_left hqne hmul
  exact_mod_cast hd

/-- Every genuine word/anchor candidate satisfies the exact divisibility test
    over the integers; the witness quotient is the terminal parameter. -/
theorem formal_inverse_terminal_divides
    {d R c : Nat} {w : List InverseLetter}
    (hp : FormalInversePath (d:Int) w (R:Int) (c:Int)) :
    (terminalDenom w : Int) ∣ terminalNumerator c w := by
  refine ⟨(d:Int), ?_⟩
  exact (formal_inverse_terminal_candidate hp).symm

/-- Along a genuine terminal-seeded path the signed candidate numerator is
    nonnegative. -/
theorem formal_inverse_terminal_numerator_nonneg
    {d R c : Nat} {w : List InverseLetter}
    (hp : FormalInversePath (d:Int) w (R:Int) (c:Int)) :
    0 ≤ terminalNumerator c w := by
  rw [← formal_inverse_terminal_candidate hp]
  exact Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)

#print axioms terminalDenom_identity
#print axioms terminalDenom_mod6
#print axioms formal_inverse_terminal_candidate
#print axioms formal_inverse_terminal_unique
#print axioms formal_inverse_terminal_divides
#print axioms formal_inverse_terminal_numerator_nonneg

end BB6.Agent31F321Density
