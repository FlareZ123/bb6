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

end BB6.Agent30Generic
