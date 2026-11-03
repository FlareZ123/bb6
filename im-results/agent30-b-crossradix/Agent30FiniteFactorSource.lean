import Agent30CrossRadixSource
import Agent30BFiniteFactor

namespace BB6.Agent30Cross

/-- Complete finite quotient classification of the unmodified B scalar source. -/
theorem source_finite_factor_iff (n m : Nat) (hn : 0<n) (hm : 0<m) :
    (∀ x y : Nat, x%m=y%m →
      BB6.OneDim.iterG n x % m = BB6.OneDim.iterG n y % m) ↔ m ∣ 7 := by
  simpa only [←iterG_eq_source] using (iterG_finite_factor_iff n m hn hm)

#print axioms source_finite_factor_iff
end BB6.Agent30Cross
