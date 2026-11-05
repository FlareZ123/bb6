import SheepChainRoot
import ChainSourceWitnesses

namespace SheepFullBasin

theorem at_most_three
    (R m c z M C Z : Nat)
    (hroot : ∀ x, SheepEven.EvenEdge x R → x%2=0 → m*x+c=z*R)
    (hmid : ∀ x y, SheepEven.EvenEdge x y → x%2=0 →
      m*y+c=z*R → M*x+C=Z*R)
    (hleaf : ∀ x y, SheepEven.EvenEdge x y → x%2=0 →
      M*y+C=Z*R → False)
    {x : Nat} (hx : x%2=0) (hr : SheepEven.EvenReach x R) :
    x=R ∨ m*x+c=z*R ∨ M*x+C=Z*R := by
  induction hr with
  | refl x => exact Or.inl rfl
  | @cons x mid y edge tail ih =>
    have heven : mid%2=0 := SheepEven.even_edge_even edge
    rcases ih hroot hmid hleaf heven with h0 | h1 | h2
    · subst mid
      exact Or.inr (Or.inl (hroot x edge hx))
    · exact Or.inr (Or.inr (hmid x mid edge hx h1))
    · exact False.elim (hleaf x mid edge hx h2)

#print axioms at_most_three
end SheepFullBasin
