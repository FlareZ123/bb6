import ParityAffineGeneral
import Agent10BSource
namespace BB6.Agent30Generic
theorem B_G_eq_H (z : Nat) :
    BB6.OneDim.G z = H 3 4 5 z := rfl

theorem B_iterG_eq_iterH (n z : Nat) :
    BB6.OneDim.iterG n z = iterH 3 4 5 n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    change BB6.OneDim.iterG n (BB6.OneDim.G z) =
      iterH 3 4 5 n (H 3 4 5 z)
    rw [B_G_eq_H]
    exact ih (H 3 4 5 z)

theorem B_affine_modulus_iff_dvd_seven (n m : Nat) (hn:0<n) :
    (∃ a b : Nat, ∀ z, (BB6.OneDim.iterG n z)%m=(a*z+b)%m) ↔ m∣7 := by
  have h := iterH_affine_modulus_iff_gap 3 4 5 n m (by decide) (by decide) hn
  change (∃ a b : Nat, ∀ z, (iterH 3 4 5 n z)%m=(a*z+b)%m) ↔ m∣7 at h
  simpa only [B_iterG_eq_iterH] using h

#print axioms B_affine_modulus_iff_dvd_seven
end BB6.Agent30Generic
