import ZeroAncestry
import CounterBridge

namespace BB6.Agent39Sheep

/-- The exact arithmetic parent is a genuine generic Sheep section return. -/
theorem parent_is_actual {x y : Nat} (hp : Parent0 x y) :
    SheepBridge.SectionNext x y := by
  rcases hp with ⟨hge, hodd, hxy⟩
  have hy : x + (x-1)/2 = y := by omega
  have he := SheepBridge.SectionNext.general 0 x hge hodd
  simpa only [Nat.pow_zero, Nat.one_mul, Nat.zero_add, hy] using he

/-- Every all-zero-valuation chain consists of real counter-machine transitions. -/
theorem chain_is_actual {h x y : Nat} (c : Chain0 h x y) :
    SheepBridge.Steps (x-3,1) (y-3,1) := by
  induction c with
  | nil x => exact SheepBridge.Steps.refl _
  | @cons n x mid y edge tail ih =>
      have hstep := SheepBridge.section_edge_counter_sound (parent_is_actual edge)
      exact SheepBridge.Steps.trans hstep ih

/-- Any target at least five with divisible offset has a concrete all-generic
    predecessor chain realized as a true finite counter trajectory. -/
theorem section_ancestor_of_divisible (h y : Nat) (hy : 5≤y)
    (hd : 3^h ∣ y-1) :
    ∃ x, Chain0 h x y ∧ SheepBridge.Steps (x-3,1) (y-3,1) := by
  obtain ⟨x,hchain⟩ := (chain_target_iff_divisible h y hy).mpr hd
  exact ⟨x, hchain, chain_is_actual hchain⟩

#print axioms BB6.Agent39Sheep.parent_is_actual
#print axioms BB6.Agent39Sheep.section_ancestor_of_divisible
end BB6.Agent39Sheep
