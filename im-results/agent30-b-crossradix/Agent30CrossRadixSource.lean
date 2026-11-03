import BOneDim
import Agent30CrossRadix

namespace BB6.Agent30Cross

theorem iterG_eq_source (n z : Nat) :
    iterG n z = BB6.OneDim.iterG n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    change G (iterG n z) = BB6.OneDim.iterG n (G z)
    rw [←ih (G z)]
    exact (iterG_commutes n z).symm

theorem source_cross_radix (n x y m : Nat) :
    (BB6.OneDim.iterG n x % (3^n*m) = BB6.OneDim.iterG n y % (3^n*m)) ↔
    (x % (2^n*m) = y % (2^n*m)) := by
  simpa only [←iterG_eq_source] using (iterG_cong n x y m)

#print axioms iterG_eq_source
#print axioms source_cross_radix
end BB6.Agent30Cross
