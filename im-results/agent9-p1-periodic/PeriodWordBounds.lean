import PeriodWord

namespace PeriodWord

def loss : List Nat → Nat
  | [] => 0
  | t :: ts => (2^t-1) + 2^(t+1) * loss ts

theorem pow_pos (n : Nat) : 0 < 2^n := by exact Nat.pow_pos (by decide)

theorem pow_succ_lt (n : Nat) : 2^n < 2^(n+1) := by
  rw [Nat.pow_succ]
  have h := pow_pos n
  omega

theorem cost_weight_loss (w : List Nat) :
    2^(cost w) = weight w + loss w + 1 := by
  induction w with
  | nil => decide
  | cons t ts ih =>
      simp only [cost, weight, loss]
      rw [Nat.pow_add, Nat.pow_succ]
      rw [ih]
      have ht : 0 < 2^t := pow_pos t
      have hpow : 2^t + (2^t-1) + 1 = 2^(t+1) := by
        rw [Nat.pow_succ]
        omega
      simp only [Nat.mul_add, Nat.mul_one]
      omega

theorem marker_bound (w : List Nat) : weight w < 2^(cost w) := by
  have h := cost_weight_loss w
  omega

theorem loss_zero_iff (w : List Nat) :
    loss w = 0 ↔ ∀ t ∈ w, t = 0 := by
  induction w with
  | nil => simp [loss]
  | cons t ts ih =>
      constructor
      · intro hz
        have hzero : t=0 := by
          by_cases h : t=0
          · exact h
          · have ht : 0 < t := by omega
            have hp : 1 < 2^t := Nat.one_lt_two_pow (by omega)
            simp only [loss] at hz
            omega
        have ht : loss ts = 0 := by
          simp only [loss] at hz
          have hp := pow_pos (t+1)
          have hm : 2^(t+1) * loss ts = 0 := by omega
          by_cases hts : loss ts=0
          · exact hts
          · have hp2 : 0 < loss ts := Nat.pos_of_ne_zero hts
            have hh := Nat.mul_pos hp hp2
            omega
        intro x hx
        rcases List.mem_cons.mp hx with h|h
        · simpa [h] using hzero
        · exact (ih.mp ht) x h
      · intro h
        have ht : t=0 := h t (List.mem_cons_self)
        have hts : loss ts=0 := ih.mpr (by
          intro x hx
          exact h x (List.mem_cons_of_mem t hx))
        simp [loss, ht, hts]

theorem nonzero_word_marker_lt (w : List Nat)
    (hp : ∃ t ∈ w, 0 < t) : weight w + 1 < 2^(cost w) := by
  have hneq : loss w ≠ 0 := by
    intro hz
    obtain ⟨t, ht, hpos⟩ := hp
    have hz0 := (loss_zero_iff w).mp hz t ht
    omega
  have h := cost_weight_loss w
  omega

#print axioms cost_weight_loss
#print axioms nonzero_word_marker_lt
end PeriodWord
