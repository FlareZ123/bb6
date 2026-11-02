import SQuantitative
import Init.Omega
namespace BB6.Agent9SExponentialGap
open BB6.Agent9SExp
open BB6.Agent9SDisjoint
open BB6.Agent9SQuantitative

/-- Excess over the 13-unit separation barrier grows by at least 4/3. -/
theorem gap_one (x y : Nat) (hx : 16 ≤ x) (hy : 16 ≤ y)
    (hxy : x+14≤y) :
    4*(y-x-13) ≤ 3*(nextQ y-nextQ x-13) := by
  have hlo := nextQ_lower y hy
  have hup := nextQ_upper x hx
  have hsep := nextQ_gap_growth x y 14 hx hy (by omega) hxy
  omega

theorem gap_all (x y n : Nat) (hx : 16 ≤ x) (hy : 16 ≤ y)
    (hxy : x+14≤y) :
    4^n*(y-x-13) ≤
      3^n*(iterQ y n-iterQ x n-13) := by
  induction n with
  | zero => simp [iterQ]
  | succ n ih =>
    have hs := iterQ_separation x y n hx hy hxy
    have hs' := gap_one (iterQ x n) (iterQ y n)
      (iterQ_ge x hx n) (iterQ_ge y hy n) hs
    calc
      4^(n+1)*(y-x-13) = 4*(4^n*(y-x-13)) := by
        simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 4*(3^n*(iterQ y n-iterQ x n-13)) := Nat.mul_le_mul_left _ ih
      _ = 3^n*(4*(iterQ y n-iterQ x n-13)) := by ac_rfl
      _ ≤ 3^n*(3*(nextQ (iterQ y n)-nextQ (iterQ x n)-13)) :=
        Nat.mul_le_mul_left _ hs'
      _ = 3^(n+1)*(iterQ y (n+1)-iterQ x (n+1)-13) := by
        simp [iterQ, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Original-root accelerated S counters diverge exponentially at arbitrary epochs. -/
theorem roots_gap_exp (a b : Nat) :
    (3^(min a b) * (iterQ 141 b-iterQ 17 a-13) ≥ 3*4^(min a b)) ∨
    (3^(min a b) * (iterQ 17 a-iterQ 141 b-13) ≥ 3*4^(min a b)) := by
  by_cases h : b ≤ a
  · rcases q17_distant16 (a-b) with hlo | hhi
    · have hg := gap_all (iterQ 17 (a-b)) 141 b
        (iterQ_ge 17 (by omega) (a-b)) (by omega) (by omega)
      have hnear : 3 ≤ 141-iterQ 17 (a-b)-13 := by omega
      have hmult : 3*4^b ≤ 4^b*(141-iterQ 17 (a-b)-13) :=
        by simpa [Nat.mul_comm] using (Nat.mul_le_mul_left (4^b) hnear)
      have heq : a-b+b = a := by omega
      rw [← iterQ_add, heq] at hg
      left
      rw [Nat.min_eq_right h]
      omega
    · have hg := gap_all 141 (iterQ 17 (a-b)) b
        (by omega) (iterQ_ge 17 (by omega) (a-b)) (by omega)
      have hnear : 3 ≤ iterQ 17 (a-b)-141-13 := by omega
      have hmult : 3*4^b ≤ 4^b*(iterQ 17 (a-b)-141-13) :=
        by simpa [Nat.mul_comm] using (Nat.mul_le_mul_left (4^b) hnear)
      have heq : a-b+b = a := by omega
      rw [← iterQ_add, heq] at hg
      right
      rw [Nat.min_eq_right h]
      omega
  · have hsep : 17+14 ≤ iterQ 141 (b-a) := by
      have hm := iterQ_mono 141 0 (b-a) (by omega) (by omega)
      simp only [iterQ] at hm
      omega
    have hg := gap_all 17 (iterQ 141 (b-a)) a (by omega)
      (iterQ_ge 141 (by omega) (b-a)) hsep
    have hnear : 3 ≤ iterQ 141 (b-a)-17-13 := by
      have hm := iterQ_mono 141 0 (b-a) (by omega) (by omega)
      simp only [iterQ] at hm
      omega
    have hmult : 3*4^a ≤ 4^a*(iterQ 141 (b-a)-17-13) :=
      by simpa [Nat.mul_comm] using (Nat.mul_le_mul_left (4^a) hnear)
    have heq : b-a+a=b := by omega
    rw [← iterQ_add, heq] at hg
    left
    rw [Nat.min_eq_left (by omega)]
    omega

#print axioms BB6.Agent9SExponentialGap.roots_gap_exp
end BB6.Agent9SExponentialGap
