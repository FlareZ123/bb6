import Std

namespace BB6.Agent8Zero

/-- Exact cumulative inverse cost, forced by critical mass and the
    genuine-root-compatible zero-even parametric feeder. -/
theorem exact_cost_from_rigidity
    (n b d m j : Nat)
    (hroot : b+d+2*m+2*n+13=14*2^n)
    (hb : b=4*(2^j+j))
    (hd : d+2*j+3=10*2^j) :
    7*2^j+n+m+j+5=7*2^n := by
  omega

private theorem exponential_dominates_linear
    (n : Nat) (hn : 5 ≤ n) : 4*n+8 ≤ 2^n := by
  have h : ∀ x : Nat, 4*(x+5)+8 ≤ (2:Nat)^(x+5) := by
    intro x
    induction x with
    | zero => decide
    | succ x ih =>
        have hidx : (x+1)+5=(x+5)+1 := by omega
        rw [hidx, Nat.pow_succ]
        omega
  have hidx : (n-5)+5=n := by omega
  simpa only [hidx] using h (n-5)

/-- Every genuine-root-compatible zero-even critical feeder has an
    index below its critical exponent and exponentially high inverse cost. -/
theorem zero_even_exact_cost_and_lower
    (n b d m j : Nat) (hn : 14 ≤ n)
    (hroot : b+d+2*m+2*n+13=14*2^n)
    (hb : b=4*(2^j+j))
    (hd : d+2*j+3=10*2^j) :
    j<n ∧
    7*2^j+n+m+j+5=7*2^n ∧
    7*2^n ≤ 2*m+4*n+8 ∧
    3*2^n ≤ m := by
  have hEq := exact_cost_from_rigidity n b d m j hroot hb hd
  have hjn : j<n := by
    by_cases hj : j<n
    · exact hj
    · have hge : n≤j := by omega
      have hp := Nat.pow_le_pow_right (show 0<(2:Nat) by decide) hge
      omega
  have hj1 : j+1≤n := by omega
  have hpow := Nat.pow_le_pow_right (show 0<(2:Nat) by decide) hj1
  have hdouble : (2:Nat)^(j+1) = 2*2^j := by rw [Nat.pow_succ]; omega
  have hp : 2*2^j ≤ 2^n := by omega
  have hcost : 7*2^n ≤ 2*m+4*n+8 := by omega
  have hdom := exponential_dominates_linear n (by omega)
  have hstrong : 3*2^n ≤ m := by omega
  exact ⟨hjn,hEq,hcost,hstrong⟩

#print axioms BB6.Agent8Zero.zero_even_exact_cost_and_lower
end BB6.Agent8Zero
