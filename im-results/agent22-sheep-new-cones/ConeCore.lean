import EvenReach
namespace Agent22SheepCones

theorem no_reach_if_reverse_closed {B : Nat → Prop} {start target : Nat}
    (hroot : B target) (hstart : ¬ B start)
    (hclosed : ∀ {x y}, SheepEven.EvenEdge x y → B y → B x) :
    ¬ SheepEven.EvenReach start target := by
  intro hpath
  have go {x y : Nat} (h : SheepEven.EvenReach x y) : B y → B x := by
    induction h with
    | refl x => exact id
    | @cons x y z edge tail ih =>
      intro hz
      exact hclosed edge (ih hz)
  exact hstart (go hpath hroot)

theorem not_10_at_node (j s d c : Nat) (hj : 20 ≤ j)
    (hbound : d*10+c < 2^20) : ¬ (d*10+c=2^(j+s)) := by
  have hp : (2:Nat)^20 ≤ 2^(j+s) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

#print axioms no_reach_if_reverse_closed
#print axioms not_10_at_node
theorem no_reach_without_incoming {start target : Nat}
    (hdifferent : start ≠ target)
    (hno : ∀ x, ¬ SheepEven.EvenEdge x target) :
    ¬ SheepEven.EvenReach start target := by
  apply no_reach_if_reverse_closed (B := fun x => x = target) rfl hdifferent
  intro x y edge hy
  subst y
  exact False.elim (hno x edge)

#print axioms no_reach_without_incoming
end Agent22SheepCones
