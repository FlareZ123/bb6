import Agent10BParity

namespace BB6.Agent10B

/-- Every two scalar cycles at least double the payload plus ten. -/
theorem G_two_growth (z : Nat) : 2*z+10 ≤ G (G z) := by
  simp only [G]
  omega

/-- Exact base-two exponential lower growth across even iteration counts. -/
theorem G_even_exp_growth (n z : Nat) :
    2^n*(z+10) ≤ iterG (2*n) z+10 := by
  induction n generalizing z with
  | zero => simp [iterG]
  | succ n ih =>
    have h := ih (G (G z))
    have hg := G_two_growth z
    have hi : 2*(z+10) ≤ G (G z)+10 := by omega
    have hm := Nat.mul_le_mul_left (2^n) hi
    have hs : iterG (2*(n+1)) z = iterG (2*n) (G (G z)) := by
      have ha : 2*(n+1)=2*n+2 := by omega
      rw [ha]
      rfl
    have hp : 2^(n+1)*(z+10)=2^n*(2*(z+10)) := by
      simp [Nat.pow_succ]
      ac_rfl
    rw [hs, hp]
    omega

theorem G_step_grows (z : Nat) : z+4 ≤ G z := by
  simp only [G]
  omega

theorem G_iter_growth (n z : Nat) : z+4*n ≤ iterG n z := by
  induction n generalizing z with
  | zero => simp [iterG]
  | succ n ih =>
    change z+4*(n+1) ≤ iterG n (G z)
    have hstep := G_step_grows z
    have h := ih (G z)
    omega

theorem G_iter_add (m n z : Nat) :
    iterG (m+n) z=iterG n (iterG m z) := by
  induction m generalizing z with
  | zero => simp [iterG]
  | succ m ih =>
    have hh : m+1+n=(m+n)+1 := by omega
    rw[hh]
    change iterG (m+n) (G z) = iterG n (iterG m (G z))
    exact ih (G z)

/-- Exponential payload growth at arbitrary lengths, with no parity assumption. -/
theorem G_all_time_exp (n : Nat) :
    10*2^(n/2) ≤ iterG n 0 +10 := by
  have hi := G_even_exp_growth (n/2) 0
  have hm : 2*(n/2)≤n := by omega
  have ht : n=2*(n/2)+(n%2) := by omega
  have hg := G_iter_growth (n%2) (iterG (2*(n/2)) 0)
  have hdecomp : iterG n 0 = iterG (n%2) (iterG (2*(n/2)) 0) := by
    calc
      iterG n 0 = iterG (2*(n/2)+(n%2)) 0 := by rw [←ht]
      _ = iterG (n%2) (iterG (2*(n/2)) 0) := G_iter_add _ _ _
  simp only [Nat.zero_add] at hi
  rw [hdecomp]
  have hmul : 10*2^(n/2) = 2^(n/2)*10 := by ac_rfl
  rw [hmul]
  omega

#print axioms G_two_growth
#print axioms G_even_exp_growth
#print axioms G_all_time_exp
end BB6.Agent10B
