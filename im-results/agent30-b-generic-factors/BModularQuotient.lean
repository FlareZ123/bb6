import ModularQuotient
import BGenericBridge

namespace BB6.Agent30Generic

/-- For each positive iterate of the source Machine B scalar map, every
    all-input standard residue quotient has modulus dividing seven.
    This consequence was independently established for B itself in the
    earlier Agent30Cross finite-factor theorem. -/
theorem B_iterG_modular_factors_iff_seven
    (n m : Nat) (hn : 0<n) (hm : 0<m) :
    (∀ x y, x%m=y%m →
       (BB6.OneDim.iterG n x)%m=(BB6.OneDim.iterG n y)%m) ↔ m∣7 := by
  have h := iterH_modular_factors_iff_gap 3 4 5 n m (by decide)
    (by decide) hn hm
  change (∀ x y, x%m=y%m → (iterH 3 4 5 n x)%m =
    (iterH 3 4 5 n y)%m) ↔ m∣7 at h
  simpa only [B_iterG_eq_iterH] using h

#print axioms B_iterG_modular_factors_iff_seven
end BB6.Agent30Generic
