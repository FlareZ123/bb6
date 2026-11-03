import Agent10BSource
import AffineBarrier

namespace BB6.Agent10IterBarrier

private theorem old_iter_succ_front (n z : Nat) :
    BB6.Agent10B.iterG (n+1) z =
    BB6.Agent10B.G (BB6.Agent10B.iterG n z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    change BB6.Agent10B.iterG (n+1) (BB6.Agent10B.G z) =
      BB6.Agent10B.G (BB6.Agent10B.iterG (n+1) z)
    exact ih (BB6.Agent10B.G z)

private theorem F_eq_old_iter (n z : Nat) :
    F n z = BB6.Agent10B.iterG n z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change G (F n z) = BB6.Agent10B.iterG (n+1) z
    rw [ih, old_iter_succ_front]
    rfl

/-- Original-source scalar map: every affine quotient of a positive iterate
    has modulus dividing 7. -/
theorem source_iter_affine_modulus_divides_seven (n m a b : Nat)
    (hn : 0<n)
    (ha : ∀ z : Nat,
      BB6.OneDim.iterG n z % m = (a*z+b)%m) : m ∣ 7 := by
  apply affine_modulus_divides_seven n m a b hn
  intro z
  rw [F_eq_old_iter, BB6.Agent10B.iterG_eq_source]
  exact ha z

#print axioms source_iter_affine_modulus_divides_seven
end BB6.Agent10IterBarrier
