import Box28Orbit
import Box28GrowthParent

namespace BB6.Agent17.Box28FirstHole
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode slot Witness)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def otherD0 : List (Fin 25) := [2,3,4,17,18,19,20]

/-- The first free slot for each canonical D0 other than 14 and 16.
    The definition is also total for inputs outside otherD0. -/
def nextIndex (d0 : Fin 25) : Fin 12 := if d0.val < 17 then 3 else 8

def cylinder (d0 v : Fin 25) : PartialMachine :=
  refine (Box28Simple.cylinder d0 none) (slot (nextIndex d0)) (decode v)

def witness (d0 v : Fin 25) : Option Witness :=
  match d0.val,v.val with
  | 2,0 => some (.halt 5)
  | 2,2 => some (.cycle 0 6 true (-1))
  | 2,5 => some (.cycle 8 1 false (-2))
  | 2,7 => some (.cycle 8 1 false (-2))
  | 2,9 => some (.cycle 0 8 true (-1))
  | 2,10 => some (.cycle 0 14 true (-1))
  | 2,11 => some (.cycle 2 4 true (-1))
  | 2,14 => some (.cycle 0 7 true (-1))
  | 2,16 => some (.cycle 0 7 true (-1))
  | 3,0 => some (.halt 5)
  | 3,5 => some (.cycle 8 1 false (-4))
  | 3,6 => some (.cycle 2 6 false 0)
  | 3,7 => some (.cycle 8 1 false (-4))
  | 3,9 => some (.cycle 2 4 false 0)
  | 3,10 => some (.cycle 2 6 false 0)
  | 3,11 => some (.cycle 2 4 false 0)
  | 4,0 => some (.halt 5)
  | 4,2 => some (.cycle 0 6 true (-1))
  | 4,5 => some (.cycle 9 1 false (-3))
  | 4,7 => some (.cycle 9 1 false (-3))
  | 17,0 => some (.halt 4)
  | 17,1 => some (.cycle 0 5 false 1)
  | 17,2 => some (.cycle 0 5 false 1)
  | 17,5 => some (.cycle 6 1 false (-4))
  | 17,6 => some (.cycle 6 1 false (-2))
  | 17,7 => some (.cycle 6 1 false (-4))
  | 17,8 => some (.cycle 1 4 false 1)
  | 17,9 => some (.cycle 5 1 false (-3))
  | 17,10 => some (.cycle 5 1 false (-1))
  | 17,11 => some (.cycle 5 1 false (-3))
  | 17,12 => some (.cycle 2 4 false 0)
  | 17,13 => some (.cycle 3 2 false (-1))
  | 17,14 => some (.cycle 3 2 true (-2))
  | 17,15 => some (.cycle 3 2 false (-1))
  | 17,17 => some (.cycle 4 1 false (-2))
  | 17,19 => some (.cycle 4 1 false (-2))
  | 18,0 => some (.halt 4)
  | 18,1 => some (.cycle 0 5 false 1)
  | 18,5 => some (.cycle 6 1 false (-2))
  | 18,7 => some (.cycle 6 1 false (-2))
  | 18,9 => some (.cycle 5 1 false (-1))
  | 18,10 => some (.cycle 8 1 false 2)
  | 18,11 => some (.cycle 5 1 false (-1))
  | 18,13 => some (.cycle 3 2 true (-1))
  | 18,17 => some (.cycle 4 1 false 0)
  | 18,19 => some (.cycle 4 1 false 0)
  | 19,0 => some (.halt 4)
  | 19,1 => some (.cycle 0 5 false 1)
  | 19,5 => some (.cycle 6 1 false (-4))
  | 19,7 => some (.cycle 6 1 false (-4))
  | 19,9 => some (.cycle 5 1 false (-3))
  | 19,10 => some (.cycle 2 3 false 0)
  | 19,11 => some (.cycle 5 1 false (-3))
  | 19,13 => some (.cycle 3 2 false (-1))
  | 19,15 => some (.cycle 3 2 false (-1))
  | 19,17 => some (.cycle 4 1 false (-2))
  | 19,19 => some (.cycle 4 1 false (-2))
  | 20,0 => some (.halt 4)
  | 20,9 => some (.cycle 2 3 false 0)
  | 20,11 => some (.cycle 2 3 false 0)
  | _,_ => none

theorem checks : ∀ d0 v : Fin 25,
    Box28Simple.accepted (cylinder d0 v) (witness d0 v) = true := by decide

def closed (d0 v : Fin 25) : Bool :=
  (witness d0 v).isSome || (d0 == 2 && v == 6)

def residual (d0 : Fin 25) : List (Fin 25) :=
  (List.finRange 25).filter (fun v => !(closed d0 v))

theorem residual_count : (otherD0.flatMap fun d => residual d).length = 114 := by decide

theorem parent_compatible (m : Machine) (hm : Fits raw10Remainder[28]! m)
    (d0 v : Fin 25) (h0 : m (3,false) = decode d0)
    (hv : m (slot (nextIndex d0)) = decode v) : compatible (cylinder d0 v) m := by
  unfold cylinder
  rw [← hv]
  exact compatible_refine _ _ _ (Box28Simple.compatible_parent m hm d0 none h0 (by simp))

theorem closed_bound (B : Nat) (hB : 11 ≤ B) (m : Machine)
    (hm : Fits raw10Remainder[28]! m) (d0 v : Fin 25)
    (h0 : m (3,false) = decode d0) (hv : m (slot (nextIndex d0)) = decode v)
    (hc : closed d0 v = true) : WeightedBound B m := by
  simp only [closed,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at hc
  rcases hc with hw | ⟨h0',hv'⟩
  · have hb := Box28Simple.witness_sound _ _ (checks d0 v) hw m (parent_compatible m hm d0 v h0 hv)
    intro k j hk hj
    exact Nat.le_trans (hb k j hk hj) hB
  · subst d0
    subst v
    exact Box28GrowthParent.parent_bound B m hm h0 hv

theorem d0_bound (B : Nat) (hB : 11 ≤ B) (d0 : Fin 25)
    (h : ∀ v ∈ residual d0, ∀ m, Fits raw10Remainder[28]! m →
      m (3,false) = decode d0 → m (slot (nextIndex d0)) = decode v → WeightedBound B m)
    (m : Machine) (hm : Fits raw10Remainder[28]! m)
    (h0 : m (3,false) = decode d0) : WeightedBound B m := by
  obtain ⟨v,he⟩ := Box28Orbit.decode_surjective (m (slot (nextIndex d0)))
  by_cases hc : closed d0 v = true
  · exact closed_bound B hB m hm d0 v h0 he.symm hc
  · apply h v ?_ m hm h0 he.symm
    simp [residual,hc]

#print axioms closed_bound
#print axioms d0_bound
end BB6.Agent17.Box28FirstHole
