import SExponentialGap
import Init.Omega
namespace BB6.Agent9SSkipCone
open BB6.Agent9SExp BB6.Agent9SDisjoint BB6.Agent9SQuantitative BB6.Agent9SExponentialGap

/-- If another starting point lies at least fourteen away from both ends
of a forward step of x, the two entire q-trajectories never coalesce,
with arbitrary asynchronous time shifts. -/
theorem skip_cone (x y k a b : Nat) (hx : 16 ≤ x)
    (hlo : iterQ x k+14 ≤ y)
    (hhi : y+14 ≤ iterQ x (k+1)) :
    (iterQ x a + (14+min a b) ≤ iterQ y b) ∨
    (iterQ y b + (14+min a b) ≤ iterQ x a) := by
  have hy : 16 ≤ y := by
    have hh := iterQ_ge x hx k
    omega
  by_cases h : b ≤ a
  · by_cases hlt : a-b ≤ k
    · have hm := iterQ_mono x (a-b) k hx hlt
      have hs : iterQ x (a-b)+14 ≤ y := by omega
      have hg := iterQ_gap_growth (iterQ x (a-b)) y 14 b
        (iterQ_ge x hx (a-b)) hy (by omega) hs
      have heq : a-b+b = a := by omega
      rw [← iterQ_add, heq] at hg
      left
      rw [Nat.min_eq_right h]
      exact hg
    · have hm := iterQ_mono x (k+1) (a-b) hx (by omega)
      have hs : y+14 ≤ iterQ x (a-b) := by omega
      have hg := iterQ_gap_growth y (iterQ x (a-b)) 14 b
        hy (iterQ_ge x hx (a-b)) (by omega) hs
      have heq : a-b+b = a := by omega
      rw [← iterQ_add, heq] at hg
      right
      rw [Nat.min_eq_right h]
      exact hg
  · have hm := iterQ_mono y 0 (b-a) hy (by omega)
    simp only [iterQ] at hm
    have hmonox := iterQ_mono x 0 k hx (by omega)
    simp only [iterQ] at hmonox
    have hs : x+14 ≤ iterQ y (b-a) := by omega
    have hg := iterQ_gap_growth x (iterQ y (b-a)) 14 a
      hx (iterQ_ge y hy (b-a)) (by omega) hs
    have heq : b-a+a=b := by omega
    rw [← iterQ_add, heq] at hg
    left
    rw [Nat.min_eq_left (by omega)]
    exact hg

/-- Every integer in the large finite gap between the eighth and ninth
accelerated S counter values from 17 is permanently separated. -/
theorem root17_interval (y a b : Nat)
    (hlo : 139 ≤ y) (hhi : y ≤ 151) :
    (iterQ 17 a + (14+min a b) ≤ iterQ y b) ∨
    (iterQ y b + (14+min a b) ≤ iterQ 17 a) := by
  apply skip_cone 17 y 8 a b (by omega)
  · have hv : iterQ 17 8 = 125 := by decide
    rw [hv]
    omega
  · have hv : iterQ 17 9 = 165 := by decide
    simpa only [hv] using (show y+14 ≤ 165 by omega)

/-- An integer q at least 97 advances by at least 28 in one q step. -/
theorem nextQ_jump28 (q : Nat) (hq : 97 ≤ q) :
    q+28 ≤ nextQ q := by
  have hg := nextQ_lower q (by omega)
  omega

/-- The original q17 counter is above the step-jump threshold by epoch nine. -/
theorem root17_large (k : Nat) :
    97 ≤ iterQ 17 (k+9) := by
  have hm := iterQ_mono 17 9 (k+9) (by omega) (by omega)
  have hh : iterQ 17 9 = 165 := by decide
  rw [hh] at hm
  omega

/-- Explicit infinite family of synthetic S counters whose orbits remain
permanently distinct from the original q=17 trajectory at arbitrary times. -/
def escapedCounter (k : Nat) : Nat := iterQ 17 (k+9)+14

theorem escaped_ne (k a b : Nat) :
    iterQ 17 a ≠ iterQ (escapedCounter k) b := by
  have hh := skip_cone 17 (escapedCounter k) (k+9) a b (by omega)
    (by simp [escapedCounter])
    (by
      change iterQ 17 (k+9)+14+14 ≤ iterQ 17 ((k+9)+1)
      have hz := nextQ_jump28 (iterQ 17 (k+9)) (root17_large k)
      simpa [iterQ] using hz)
  rcases hh with hh | hh <;> omega

theorem escaped_injective : Function.Injective escapedCounter := by
  intro a b hab
  by_cases hlt : a < b
  · have he := iterQ_strict 17 (a+9) (by omega)
    have hm := iterQ_mono 17 (a+9+1) (b+9) (by omega) (by omega)
    unfold escapedCounter at hab
    omega
  · by_cases hgt : b < a
    · have he := iterQ_strict 17 (b+9) (by omega)
      have hm := iterQ_mono 17 (b+9+1) (a+9) (by omega) (by omega)
      unfold escapedCounter at hab
      omega
    · omega

#print axioms BB6.Agent9SSkipCone.escaped_ne
#print axioms BB6.Agent9SSkipCone.escaped_injective
#print axioms BB6.Agent9SSkipCone.skip_cone
#print axioms BB6.Agent9SSkipCone.root17_interval
end BB6.Agent9SSkipCone
