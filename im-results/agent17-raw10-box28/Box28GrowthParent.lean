import Box28GrowthSource
import Box28Simple

namespace BB6.Agent17.Box28GrowthParent
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode)

open BB6.Agent13.Box17 (slot)

theorem partial_eq :
    refine (Box28Simple.cylinder 2 none) (slot 3) (decode 6) = Box28GrowthSource.partialTable := by
  funext s
  rcases s with ⟨q,b⟩
  revert q b
  decide

theorem parent_never (m : Machine) (hm : Fits raw10Remainder[28]! m)
    (hD : m (3,false) = decode 2) (hB : m (1,true) = decode 6) : NeverHalts m := by
  have hc := Box28Simple.compatible_parent m hm 2 none hD (by simp)
  have hb := compatible_refine _ m (slot 3) hc
  rw [show m (slot 3) = decode 6 from hB,partial_eq] at hb
  exact Box28GrowthSource.compatible_never m hb

theorem parent_bound (B : Nat) (m : Machine) (hm : Fits raw10Remainder[28]! m)
    (hD : m (3,false) = decode 2) (hB : m (1,true) = decode 6) : WeightedBound B m :=
  weighted_of_never B m (parent_never m hm hD hB)

#print axioms parent_never
#print axioms parent_bound
end BB6.Agent17.Box28GrowthParent
