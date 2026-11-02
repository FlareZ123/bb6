import Lean.Elab.Tactic.Omega
namespace BB6Sheep17

/-- Exact generic inverse algebra for a symbolic target `d*y=q+b`.
If `p=2^a` and `q=2^(j+s)`, this is precisely the parent-family formula
used by symbolic_sieve.py. All variables are Int so no truncating subtraction. -/
theorem generic_parent_identity (p q u a b d x y : Int)
    (hx : x = p*u)
    (hy : d*y = q+b)
    (hr : 2*y = (2*p+1)*u + 2*a-1) :
    d*(2*p+1)*x = 2*p*q + 2*p*b + p*d*(1-2*a) := by
  have heq : d*((2*p+1)*u) = d*(2*y)-d*(2*a-1) := by
    have h := congrArg (fun z : Int => d*z) hr
    simp only [Int.mul_sub, Int.mul_add] at h ⊢
    omega
  have hmul : (2*p)*(d*y) = (2*p)*(q+b) :=
    congrArg (fun z : Int => (2*p)*z) hy
  calc
    d*(2*p+1)*x = p * (d * ((2*p+1)*u)) := by rw [hx]; ac_rfl
    _ = p * (d*(2*y)-d*(2*a-1)) := by rw [heq]
    _ = 2*p*q + 2*p*b + p*d*(1-2*a) := by
      simp only [Int.mul_add, Int.mul_sub, Int.mul_assoc] at hmul ⊢
      simp only [Int.mul_one, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] at hmul ⊢
      omega

/-- The necessary divisibility test for every generic parent. -/
theorem generic_parent_divisibility (p q u a b d y : Int)
    (hy : d*y = q+b)
    (hr : 2*y = (2*p+1)*u + 2*a-1) :
    (d*(2*p+1)) ∣ (2*q+2*b-d*(2*a-1)) := by
  refine ⟨u, ?_⟩
  have heq : d*((2*p+1)*u) = d*(2*y)-d*(2*a-1) := by
    have h := congrArg (fun z : Int => d*z) hr
    simp only [Int.mul_sub, Int.mul_add] at h ⊢
    omega
  have hy2 : 2*(d*y) = 2*(q+b) := congrArg (fun z : Int => 2*z) hy
  calc
    2*q+2*b-d*(2*a-1) = d*(2*y)-d*(2*a-1) := by
      simp only [Int.mul_add] at hy2 ⊢
      simp only [Int.mul_assoc, Int.mul_comm] at hy2 ⊢
      omega
    _ = d*((2*p+1)*u) := heq.symm
    _ = (d*(2*p+1))*u := by ac_rfl

/-- The numerical induction on the large-valuation gap, independent of
its exponential implementation. -/
theorem small_odd_gap_persists (d k p : Nat)
    (hlo : 1 < k) (hhi : k < p) (hd : 2*d <= p) :
    1 < k+2*d ∧ k+2*d < 2*p ∧ 2*d <= 2*p := by
  omega

/-- Every generic defined Sheep return step strictly increases the counter. -/
theorem generic_grows (a u : Nat) (hu : u >= 5) :
    2^a*u < 2^a*u + a + (u-1)/2 := by
  omega

/-- Every exceptional `u=3` defined Sheep return step strictly grows. -/
theorem exceptional_grows (a : Nat) :
    3*2^a < 3*2^a + a + 3 := by
  omega

/-- The induction for the odd small-remainder condition. -/
theorem gap_odd_persists (d k : Nat) (h : k%2 = 1) :
    (k+2*d)%2 = 1 := by
  omega

#print axioms generic_parent_identity
#print axioms generic_parent_divisibility
#print axioms small_odd_gap_persists
#print axioms generic_grows
#print axioms exceptional_grows
#print axioms gap_odd_persists
end BB6Sheep17
