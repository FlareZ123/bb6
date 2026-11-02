import Std
namespace BB6Sheep17Modulus

/-- If a modulus-M exponent class contains an exponent divisible by D,
then the residue is divisible by gcd(M,D). This is the necessary half
of the generalized two-congruence CRT criterion. -/
theorem corridor_residue_necessary (M D r j : Nat) (hj : D ∣ j)
    (hr : j % M = r % M) : Nat.gcd M D ∣ r := by
  have gM : M.gcd D ∣ M := Nat.gcd_dvd_left M D
  have gD : M.gcd D ∣ D := Nat.gcd_dvd_right M D
  have gj : M.gcd D ∣ j := Nat.dvd_trans gD hj
  have gjmod : M.gcd D ∣ j % M := (Nat.dvd_mod_iff gM).2 gj
  have grmod : M.gcd D ∣ r % M := by rwa [hr] at gjmod
  exact (Nat.dvd_mod_iff gM).1 grmod

#print axioms corridor_residue_necessary
end BB6Sheep17Modulus
