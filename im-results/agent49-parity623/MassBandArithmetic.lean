import Std.Tactic

/-! A generic polylogarithmic length bound for a growing two-scale path. -/
namespace BB6.Agent49MassBandArithmetic

/-- The first coordinate is total mass, the second a nonnegative smaller
coordinate bounded by mass. A step either multiplies mass by at least 6/5
or doubles the shifted smaller coordinate. -/
inductive Path : Nat → Nat → Nat → Nat → Nat → Prop where
  | zero (s m : Nat) (hm : m ≤ s) : Path 0 s m s m
  | step {k s m u v x y : Nat} : Path k s m u v → u ≤ x → y ≤ x →
      (6*u ≤ 5*x ∨ 2*(v+1) ≤ y+1) → Path (k+1) s m x y

private theorem pow_index_le {i N : Nat} (h : 2^i ≤ 2^N) : i ≤ N := by
  by_cases h' : i ≤ N
  · exact h'
  · have hp := Nat.pow_lt_pow_right (by decide : 1<2) (show N<i by omega)
    omega

private theorem big_pow (N i : Nat) : 2^N * 5^(4*N+i) ≤ 6^(4*N+i) := by
  have h := Nat.pow_le_pow_left (show 2*5^4 ≤ 6^4 by decide) N
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at h
  rw [Nat.pow_add, Nat.pow_add, ← Nat.mul_assoc]
  exact Nat.mul_le_mul h (Nat.pow_le_pow_left (by decide) i)

/-- Counts the multiplying steps and the final run of smaller-coordinate
steps. A run of the latter fits at most N steps below the binary mass cap. -/
theorem path_budget {k s m x y : Nat} (h : Path k s m x y)
    (N : Nat) (hx : x < 2^N) :
    ∃ b r, 6^b*s ≤ 5^b*x ∧ 2^r ≤ y+1 ∧ r≤N ∧ k≤b*(N+1)+r := by
  induction h with
  | zero s m hm =>
    refine ⟨0,0,?_,?_,?_,?_⟩ <;> simp
  | @step k s m u v x y h hu hy he ih =>
    obtain ⟨b,r,hb,hr,hrN,hk⟩ := ih (by omega)
    rcases he with hbig | hsmall
    · refine ⟨b+1,0,?_,by simp,by omega,?_⟩
      · calc
          6^(b+1)*s = 6*(6^b*s) := by simp [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
          _ ≤ 6*(5^b*u) := Nat.mul_le_mul_left 6 hb
          _ = 5^b*(6*u) := by simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
          _ ≤ 5^b*(5*x) := Nat.mul_le_mul_left _ hbig
          _ = 5^(b+1)*x := by simp [Nat.pow_succ,Nat.mul_assoc]
      · rw [Nat.add_mul]; simp; omega
    · have hpow : 2^(r+1) ≤ y+1 := by
        rw [Nat.pow_succ]
        have h := Nat.mul_le_mul_right 2 hr
        omega
      refine ⟨b,r+1,?_,hpow,?_,by omega⟩
      · exact Nat.le_trans hb (Nat.mul_le_mul_left _ hu)
      · exact pow_index_le (Nat.le_trans hpow (by omega))

/-- Every path starting at positive mass and ending below 2^N has at most
4N²+5N steps. This bound is uniform in the initial smaller coordinate. -/
theorem path_length {k s m x y : Nat} (h : Path k s m x y)
    (hs : 0<s) (N : Nat) (hx : x<2^N) : k ≤ 4*N*N+5*N := by
  obtain ⟨b,r,hb,hr,hrN,hk⟩ := path_budget h N hx
  have hbN : b < 4*N := by
    by_cases hlt : b<4*N
    · exact hlt
    · have hdecomp : b=4*N+(b-4*N) := by omega
      have hp := big_pow N (b-4*N)
      rw [← hdecomp] at hp
      have hs' : 6^b ≤ 6^b*s := by
        have hh := Nat.mul_le_mul_left (6^b) (show 1≤s by omega)
        simpa using hh
      have hcontra : 2^N * 5^b ≤ x*5^b := by
        have hh := Nat.le_trans hp (Nat.le_trans hs' hb)
        simpa [Nat.mul_comm] using hh
      have hh := Nat.le_of_mul_le_mul_right hcontra (Nat.pow_pos (by decide))
      omega
  have hh := Nat.mul_le_mul_right (N+1) (show b≤4*N by omega)
  have hpoly : (4*N)*(N+1)+N = 4*N*N+5*N := by rw [Nat.mul_add]; omega
  omega

#print axioms path_budget
#print axioms path_length
end BB6.Agent49MassBandArithmetic
