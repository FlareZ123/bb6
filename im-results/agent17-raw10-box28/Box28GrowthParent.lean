import Box28GrowthSource
import Box28Simple

namespace BB6.Agent17.Box28GrowthParent
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode)

theorem parent_never (m : Machine) (hm : Fits raw10Remainder[28]! m)
    (hD : m (3,false) = decode 2) (hB : m (1,true) = decode 6) : NeverHalts m := by
  obtain ⟨ha,hb,hc,hd⟩ := Box28Simple.parent_rows m hm
  apply Box28GrowthSource.compatible_never m
  intro s t ht
  obtain ⟨q,b⟩ := s
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;>
    simp [Box28GrowthSource.partialTable] at ht
  all_goals
    subst t
    first | exact ha | exact hb | exact hc | exact hd | exact hD | exact hB

theorem parent_bound (B : Nat) (m : Machine) (hm : Fits raw10Remainder[28]! m)
    (hD : m (3,false) = decode 2) (hB : m (1,true) = decode 6) : WeightedBound B m :=
  weighted_of_never B m (parent_never m hm hD hB)

#print axioms parent_never
#print axioms parent_bound
end BB6.Agent17.Box28GrowthParent
