import Q0ExhaustiveTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Q0RosterConsume
open BB6Coverage BB6.Agent13BlankDelay Q0ExhaustiveTree

def removeCovered (frontier closed : List PartialMachine) : List PartialMachine :=
  frontier.filter fun p => !(closed.any (sameTable p))

theorem liftWeighted {A B : Nat} (hAB : A ≤ B) {m : Machine}
    (h : WeightedBound A m) : WeightedBound B m := by
  intro k d hk hd
  exact Nat.le_trans (h k d hk hd) hAB

theorem consume (B : Nat) (frontier closed : List PartialMachine)
    (hc : ∀ p ∈ closed, Cover (WeightedBound B) p)
    (hr : ∀ p ∈ removeCovered frontier closed, ∀ m, compatible p m → WeightedBound B m) :
    ∀ p ∈ frontier, ∀ m, compatible p m → WeightedBound B m := by
  intro p hp m hm
  cases h : closed.any (sameTable p) with
  | false =>
    apply hr p (List.mem_filter.mpr ⟨hp,by simp [h]⟩) m hm
  | true =>
    obtain ⟨q,hq,he⟩ := List.any_eq_true.mp h
    have heq := sameTable_sound he
    subst q
    exact (hc p hq).sound m hm

theorem liftCover {A B : Nat} {p : PartialMachine} (hAB : A ≤ B)
    (h : Cover (WeightedBound A) p) : Cover (WeightedBound B) p :=
  .leaf _ fun m hm => liftWeighted hAB (h.sound m hm)
#print axioms consume
#print axioms liftCover
end Q0RosterConsume
