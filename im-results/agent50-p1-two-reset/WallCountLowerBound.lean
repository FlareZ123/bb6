import CountFinal

set_option maxHeartbeats 2000000

namespace BB6.Agent50TwoReset
open BB6.Agent28

/-- The polynomial reset envelope has a closed monomial expression. -/
theorem budget_closed_form (n j : Nat) :
    budget n j = 24^(j+1)*(n+2)^(2*j+3) := by
  induction j with
  | zero =>
    simp [budget]
  | succ j ih =>
    have hidx : 2*(j+1)+3=(2*j+3)+2 := by omega
    calc
      budget n (j+1) = budget n j*(24*(n+2)^2) := rfl
      _ = (24^(j+1)*(n+2)^(2*j+3))*(24*(n+2)^2) := by rw [ih]
      _ = 24^((j+1)+1)*(n+2)^((2*j+3)+2) := by
          rw [Nat.pow_succ 24 (j+1), Nat.pow_add (n+2) (2*j+3) 2]
          ac_rfl
      _ = 24^((j+1)+1)*(n+2)^(2*(j+1)+3) := by rw [hidx]

/-- An unconditional necessary quantitative bound on the positive-reset
    count of any authentic source affine-wall history. -/
theorem source_wall_forces_exponential_reset_count
    (n z b d m:Nat)
    (hn:42≤n) (hz:1≤z)
    (hcount: CountCone (14*2^n-2*n-16) 3 b d m z)
    (hwall:b=4*(m+n)) :
    2^n ≤ 24^z*(n+2)^(2*z+2) := by
  have hlow : 2^n ≤ budget n (z-1)*(n+2) := by
    by_cases hle : 2^n ≤ budget n (z-1)*(n+2)
    · exact hle
    have hsmall : budget n (z-1)*(n+2)<2^n := by omega
    have hc : CountCone (14*2^n-2*n-16) 3 b d m ((z-1)+1) := by
      simpa only [Nat.sub_add_cancel hz] using hcount
    exact False.elim (counted_excludes_budgeted_wall n (z-1) b d m hn hsmall hc hwall)
  have hclosed : budget n (z-1)=24^z*(n+2)^(2*z+1) := by
    have h := budget_closed_form n (z-1)
    have hi : (z-1)+1=z := by omega
    have hi2 : 2*(z-1)+3=2*z+1 := by omega
    simpa only [hi,hi2] using h
  have hpow : (n+2)^(2*z+1)*(n+2)=(n+2)^(2*z+2) := by
    have hh := Nat.pow_succ (n+2) (2*z+1)
    have hi : (2*z+1)+1=2*z+2 := by omega
    simpa only [hi] using hh.symm
  calc
    2^n ≤ budget n (z-1)*(n+2) := hlow
    _ = 24^z*(n+2)^(2*z+2) := by
      rw [hclosed]
      calc
        (24^z*(n+2)^(2*z+1))*(n+2) =
          24^z*((n+2)^(2*z+1)*(n+2)) := by ac_rfl
        _ = 24^z*(n+2)^(2*z+2) := by rw [hpow]

#print axioms BB6.Agent50TwoReset.budget_closed_form
#print axioms BB6.Agent50TwoReset.source_wall_forces_exponential_reset_count
end BB6.Agent50TwoReset
