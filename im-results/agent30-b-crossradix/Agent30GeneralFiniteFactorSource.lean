import ParityAffineGeneral
import Agent30GeneralFiniteFactorComplete

namespace BB6.Agent30GeneralFactor

theorem iterH_commutes (r c s n z : Nat) :
    iterH r c s n (H r c s z) = H r c s (iterH r c s n z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change H r c s (iterH r c s n (H r c s z)) =
      H r c s (H r c s (iterH r c s n z))
    rw [ih]

/-- Exact correspondence to the original generic parity-affine definition. -/
theorem iterH_eq_prior_source (r c s n z : Nat) :
    iterH r c s n z = BB6.Agent30Generic.iterH r c s n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    change H r c s (iterH r c s n z) =
      BB6.Agent30Generic.iterH r c s n (H r c s z)
    rw [←ih (H r c s z)]
    exact (iterH_commutes r c s n z).symm

/-- Source-faithful generic nonlinear quotient classification. -/
theorem source_iterH_factor_iff_gap (r c s n m : Nat)
    (hr:r%2=1) (hgap:r≤2*s) (hn:0<n) (hm:0<m) :
    (∀ x y : Nat, x%m=y%m →
        BB6.Agent30Generic.iterH r c s n x % m =
        BB6.Agent30Generic.iterH r c s n y % m) ↔
    m ∣ (2*s-r) := by
  simpa only [←iterH_eq_prior_source] using
    (iterH_factor_iff_gap r c s n m hr hgap hn hm)

#print axioms iterH_eq_prior_source
#print axioms source_iterH_factor_iff_gap
end BB6.Agent30GeneralFactor
