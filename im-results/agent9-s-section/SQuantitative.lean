import SDisjoint
import Init.Omega
namespace BB6.Agent9SQuantitative
open BB6.Agent9SExp
open BB6.Agent9SDisjoint

/-- A gap of at least 14 gains at least one unit on each future q step. -/
theorem nextQ_gap_growth (a b d : Nat)
    (ha : 16 ≤ a) (hb : 16 ≤ b) (hd : 14 ≤ d)
    (h : a+d ≤ b) : nextQ a + (d+1) ≤ nextQ b := by
  have hlow := nextQ_lower b hb
  have hupp := nextQ_upper a ha
  omega

theorem iterQ_gap_growth (a b d n : Nat)
    (ha : 16 ≤ a) (hb : 16 ≤ b) (hd : 14 ≤ d)
    (h : a+d ≤ b) :
    iterQ a n + (d+n) ≤ iterQ b n := by
  induction n with
  | zero => simpa [iterQ] using h
  | succ n ih =>
    have hh := nextQ_gap_growth (iterQ a n) (iterQ b n)
      (d+n) (iterQ_ge a ha n) (iterQ_ge b hb n) (by omega) ih
    simpa [iterQ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hh

theorem q17_distant16 (k : Nat) :
    iterQ 17 k+16 ≤ 141 ∨ 141+24 ≤ iterQ 17 k := by
  by_cases hk : k ≤ 8
  · left
    have hm := iterQ_mono 17 k 8 (by omega) hk
    have heq : iterQ 17 8 = 125 := by decide
    rw [heq] at hm
    omega
  · right
    have hm := iterQ_mono 17 9 k (by omega) (by omega)
    have heq : iterQ 17 9 = 165 := by decide
    rw [heq] at hm
    omega

/-- Quantitative asynchronous root separation, sharp at a=8 and b=0. -/
theorem rooted_distance (a b : Nat) :
    (iterQ 17 a + (16+min a b) ≤ iterQ 141 b) ∨
    (iterQ 141 b + (16+min a b) ≤ iterQ 17 a) := by
  by_cases h : b ≤ a
  · rcases q17_distant16 (a-b) with hlo | hhi
    · have hg := iterQ_gap_growth (iterQ 17 (a-b)) 141 16 b
        (iterQ_ge 17 (by omega) (a-b)) (by omega) (by omega) hlo
      have eqn : a-b+b = a := by omega
      rw [← iterQ_add, eqn] at hg
      left
      have hmin : min a b = b := Nat.min_eq_right h
      rw [hmin]
      exact hg
    · have hg := iterQ_gap_growth 141 (iterQ 17 (a-b)) 24 b
        (by omega) (iterQ_ge 17 (by omega) (a-b)) (by omega) hhi
      have eqn : a-b+b = a := by omega
      rw [← iterQ_add, eqn] at hg
      right
      have hmin : min a b = b := Nat.min_eq_right h
      rw [hmin]
      omega
  · have h124 : 17+124 ≤ iterQ 141 (b-a) := by
      have hmono := iterQ_mono 141 0 (b-a) (by omega) (by omega)
      simp only [iterQ] at hmono
      omega
    have hg := iterQ_gap_growth 17 (iterQ 141 (b-a)) 124 a
      (by omega) (iterQ_ge 141 (by omega) (b-a)) (by omega) h124
    have eqn : b-a+a=b := by omega
    rw [← iterQ_add, eqn] at hg
    left
    have hmin : min a b = a := Nat.min_eq_left (by omega)
    rw [hmin]
    omega

#print axioms BB6.Agent9SQuantitative.rooted_distance
end BB6.Agent9SQuantitative
