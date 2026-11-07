import PeriodFinite
import PeriodWord

namespace PeriodFiniteWord

theorem linear_cost_bounded (w : List Nat) (m : Nat → Nat)
    (N : Nat) (hm : ∀ n<N, m (n+1) = m n + PeriodWord.cost w) :
    ∀ n≤N, m n = m 0 + PeriodWord.cost w * n := by
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev : n ≤ N := by omega
    have hstep := hm n (by omega)
    rw [hstep, ih hprev, Nat.mul_succ]
    omega

/-- Every *finite* sequence of N+1 copies of an exact scalar inverse word,
    with a nonintegral block slope, obeys a quantitative length bound. -/
theorem finite_word_bound (L : Nat) (w : List Nat) (N : Nat)
    (hw : 0 < PeriodWord.cost w)
    (m z : Nat → Nat)
    (hr : ∀ n<N+1, PeriodWord.Run L w (m n) (z n)
       (m (n+1)) (z (n+1)))
    (hbad : ∀ d:Int, (((2:Nat)^(PeriodWord.cost w):Int)-1)*d ≠
          (PeriodWord.weight w:Int)*(PeriodWord.cost w:Int)) :
    (2:Nat)^((PeriodWord.cost w)*N) ≤
       (PeriodFinite.error (2^(PeriodWord.cost w))
           (PeriodWord.weight w:Int) (PeriodWord.cost w:Int)
           (fun n => (z n:Int)) 0).natAbs := by
  have hm : ∀ n<N+1, m (n+1) = m n+PeriodWord.cost w := by
    intro n hn
    exact PeriodWord.run_cost L w (m n) (z n) (m (n+1)) (z (n+1)) (hr n hn)
  have hline := linear_cost_bounded w m (N+1) hm
  let zi : Nat → Int := fun n => (z n : Int)
  have hrec : ∀ n<N+1,
      ((2:Nat)^(PeriodWord.cost w):Int)*zi (n+1) = zi n +
      (PeriodWord.weight w:Int)*((L:Int)+(m 0:Int)) +
      ((PeriodWord.weight w:Int)*(PeriodWord.cost w:Int))*(n:Int) +
      PeriodWord.offset w := by
    intro n hn
    have hb := PeriodWord.block_affine L w (m n) (z n)
      (m (n+1)) (z (n+1)) (hr n hn)
    rw [hline n (by omega)] at hb
    dsimp [zi]
    simp only [Int.natCast_add,Int.natCast_mul] at hb
    grind
  have hA : 2≤(2:Nat)^(PeriodWord.cost w) := by
    have := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
    omega
  have hb := PeriodFinite.finite_repetition_bound
    (2^(PeriodWord.cost w)) N hA (PeriodWord.weight w:Int)
    (PeriodWord.cost w:Int) ((L:Int)+(m 0:Int))
    (PeriodWord.offset w) zi (fun n hn => hrec n hn) hbad
  simpa [Nat.pow_mul] using hb

#print axioms finite_word_bound
end PeriodFiniteWord
