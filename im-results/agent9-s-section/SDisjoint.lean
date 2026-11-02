import SExponential
import Init.Omega
namespace BB6.Agent9SDisjoint
open BB6.Agent9SExp

theorem nextQ_strict (q : Nat) (hq : 16 ≤ q) :
    q+1 ≤ nextQ q := by
  have h := nextQ_lower q hq
  omega

theorem iterQ_strict (q n : Nat) (hq : 16 ≤ q) :
    iterQ q n + 1 ≤ iterQ q (n+1) := by
  have h := nextQ_strict (iterQ q n) (iterQ_ge q hq n)
  simpa [iterQ] using h

theorem iterQ_mono_add (q m k : Nat) (hq : 16 ≤ q) :
    iterQ q m ≤ iterQ q (m+k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := iterQ_strict q (m+k) hq
    calc
      iterQ q m ≤ iterQ q (m+k) := ih
      _ ≤ iterQ q (m+(k+1)) := by
        simpa [Nat.add_assoc] using (Nat.le_of_lt hs)

theorem iterQ_mono (q m n : Nat) (hq : 16 ≤ q) (h : m ≤ n) :
    iterQ q m ≤ iterQ q n := by
  have hs := iterQ_mono_add q m (n-m) hq
  simpa [Nat.add_sub_of_le h] using hs

theorem nextQ_separation (a b : Nat) (ha : 16 ≤ a) (hb : 16 ≤ b)
    (h : a+14 ≤ b) : nextQ a + 14 ≤ nextQ b := by
  have h1 := nextQ_upper a ha
  have h2 := nextQ_lower b hb
  omega

theorem iterQ_separation (a b n : Nat) (ha : 16 ≤ a) (hb : 16 ≤ b)
    (h : a+14 ≤ b) : iterQ a n+14 ≤ iterQ b n := by
  induction n with
  | zero => simpa [iterQ] using h
  | succ n ih =>
    have hh := nextQ_separation (iterQ a n) (iterQ b n)
      (iterQ_ge a ha n) (iterQ_ge b hb n) ih
    simpa [iterQ] using hh

theorem iterQ_add (q m n : Nat) :
    iterQ q (m+n) = iterQ (iterQ q m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [Nat.add_succ, iterQ] using congrArg nextQ ih

private theorem sample8 : iterQ 17 8 = 125 := by decide
private theorem sample9 : iterQ 17 9 = 165 := by decide

theorem q17_distant (k : Nat) :
    iterQ 17 k+14 ≤ 141 ∨ 141+14 ≤ iterQ 17 k := by
  by_cases hk : k ≤ 8
  · left
    have hh := iterQ_mono 17 k 8 (by omega) hk
    rw [sample8] at hh
    omega
  · right
    have hh := iterQ_mono 17 9 k (by omega) (by omega)
    rw [sample9] at hh
    omega

/-- Two rooted initial S counters cannot fuse at any pair of epochs. -/
theorem roots_ne (a b : Nat) : iterQ 17 a ≠ iterQ 141 b := by
  by_cases h : b ≤ a
  · rcases q17_distant (a-b) with hlo | hhi
    · have hs := iterQ_separation (iterQ 17 (a-b)) 141 b
        (iterQ_ge 17 (by omega) (a-b)) (by omega) hlo
      have heq : a-b+b=a := by omega
      rw [← iterQ_add, heq] at hs
      omega
    · have hs := iterQ_separation 141 (iterQ 17 (a-b)) b
        (by omega) (iterQ_ge 17 (by omega) (a-b)) hhi
      have heq : a-b+b=a := by omega
      rw [← iterQ_add, heq] at hs
      omega
  · have hm : 17+14 ≤ iterQ 141 (b-a) := by
      have hmono := iterQ_mono 141 0 (b-a) (by omega) (by omega)
      simp only [iterQ] at hmono
      omega
    have hs := iterQ_separation 17 (iterQ 141 (b-a)) a (by omega)
      (iterQ_ge 141 (by omega) (b-a)) hm
    have heq : b-a+a=b := by omega
    rw [← iterQ_add, heq] at hs
    omega

#print axioms BB6.Agent9SDisjoint.roots_ne
end BB6.Agent9SDisjoint
