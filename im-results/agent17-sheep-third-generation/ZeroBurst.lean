import Std
namespace BB6Sheep17

theorem zero_inverse_burst (x : Nat → Int) (k : Nat)
    (h : ∀ i < k, 3*(x (i+1)-1) = 2*(x i-1)) :
    (3:Int)^k*(x k-1) = (2:Int)^k*(x 0-1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hprev : ∀ i < k, 3*(x (i+1)-1) = 2*(x i-1) := by
      intro i hi
      exact h i (Nat.lt_succ_of_lt hi)
    have hh := ih hprev
    have hk : 3*(x (k+1)-1) = 2*(x k-1) := h k (Nat.lt_succ_self k)
    calc
      (3:Int)^(k+1)*(x (k+1)-1) = 3^k*(3*(x (k+1)-1)) := by
        rw [Int.pow_succ]; ac_rfl
      _ = 3^k*(2*(x k-1)) := by rw [hk]
      _ = 2*(3^k*(x k-1)) := by ac_rfl
      _ = 2*(2^k*(x 0-1)) := by rw [hh]
      _ = 2^(k+1)*(x 0-1) := by rw [Int.pow_succ]; ac_rfl

theorem zero_inverse_step (x y : Int)
    (h : 2*y = 3*x-1) :
    3*(x-1) = 2*(y-1) := by
  omega

theorem zero_inverse_burst_from_map (x : Nat → Int) (k : Nat)
    (h : ∀ i < k, 2*(x i) = 3*(x (i+1))-1) :
    (3:Int)^k*(x k-1) = (2:Int)^k*(x 0-1) := by
  apply zero_inverse_burst x k
  intro i hi
  exact zero_inverse_step (x (i+1)) (x i) (h i hi)

theorem zero_inverse_burst_divisible (x : Nat → Int) (k : Nat)
    (h : ∀ i < k, 2*(x i) = 3*(x (i+1))-1) :
    (3:Int)^k ∣ (2:Int)^k*(x 0-1) := by
  exact ⟨x k-1, (zero_inverse_burst_from_map x k h).symm⟩

/-- A rational-exponential root d*x0=q+b stays in an exact closed-form
family along any finite run of valuation-zero inverse transitions. -/
theorem zero_burst_family (x : Nat → Int) (k : Nat) (d q b : Int)
    (hstart : d*(x 0) = q+b)
    (h : ∀ i < k, 2*(x i) = 3*(x (i+1))-1) :
    ((3:Int)^k*d)*(x k-1) = (2:Int)^k*(q+b-d) := by
  have hb := zero_inverse_burst_from_map x k h
  have hdb := congrArg (fun z : Int => d*z) hb
  have hs := congrArg (fun z : Int => (2:Int)^k*z) hstart
  simp only [Int.mul_sub, Int.mul_add, Int.mul_assoc] at hdb hs ⊢
  simp only [Int.mul_one, Int.one_mul, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] at hdb hs ⊢
  omega

#print axioms zero_inverse_burst
#print axioms zero_inverse_step
#print axioms zero_inverse_burst_from_map
#print axioms zero_inverse_burst_divisible
#print axioms zero_burst_family
end BB6Sheep17
