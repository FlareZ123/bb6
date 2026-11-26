import Raw10RefinedCut
import BlockFARBridge
import HeldBlockProof
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent49Raw10RefinedHeld
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49BoxBridge
open BB6.Agent13CrossRouteHeldLeaf109 BB6.Agent49Raw10RefinedCut
open BB6.Agent50RootFrontier BB6.Agent49Box
theorem held_exact : BB6BlockFAR.partialTable BB6BlockFAR.Held.machine = held := by
  funext s
  rcases s with ⟨q,b⟩
  have h : ∀ q : Fin 6, ∀ b : Bool,
      BB6BlockFAR.partialTable BB6BlockFAR.Held.machine (q,b) = held (q,b) := by decide +kernel
  exact h q b
theorem held_never (m : Machine) (hm : compatible held m) : NeverHalts m :=
  BB6BlockFAR.transfer_never BB6BlockFAR.Held.machine m
    (by rwa [held_exact]) BB6BlockFAR.Held.never
theorem held_weighted (B : Nat) (m : Machine) (hm : compatible held m) : WeightedBound B m :=
  weighted_of_never B m (held_never m hm)
def parentCover33 (B : Nat) (hB : 7014 ≤ B)
    (hOpen : ∀ r ∈ openBoxes accepted, ∀ m : Machine, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  BB6.Agent49Raw10RefinedCut.parentCover33 B hB (held_weighted B) hOpen
def parentCover31 (B : Nat) (hB : 7376 ≤ B)
    (bound16 : ∀ m : Machine, Fits raw10Remainder[16]! m → WeightedBound 7376 m)
    (bound17 : ∀ m : Machine, Fits raw10Remainder[17]! m → WeightedBound 7014 m)
    (hOpen : ∀ r ∈ openBoxes candidate, ∀ m : Machine, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  BB6.Agent49Raw10RefinedCut.parentCover31 B hB bound16 bound17 (held_weighted B) hOpen
#print axioms held_exact
#print axioms held_never
#print axioms parentCover33
#print axioms parentCover31
end BB6.Agent49Raw10RefinedHeld
