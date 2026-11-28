import Raw10RefinedBox12Cut
import Box12Cover

namespace BB6.Agent48Raw10RefinedBox12
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49BoxBridge
open BB6.Agent49Raw10RefinedCut BB6.Agent50RootFrontier BB6.Agent49Box
open BB6.Agent48Raw10RefinedBox12Cut

theorem parentCover29 (B : Nat) (hB : 7014 ≤ B)
    (hOpen : ∀ r ∈ openBoxes acceptedWith12, ∀ m : Machine,
      Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent13CrossRouteHeldLeaf109.firstOneB0_1LC :=
  parentCoverWith12 B hB (BB6.Agent48Box12.box12_weighted B (by omega)) hOpen

theorem parentCover27 (B : Nat) (hB : 7376 ≤ B)
    (bound16 : ∀ m : Machine, Fits raw10Remainder[16]! m → WeightedBound 7376 m)
    (bound17 : ∀ m : Machine, Fits raw10Remainder[17]! m → WeightedBound 7014 m)
    (hOpen : ∀ r ∈ openBoxes candidateWith12, ∀ m : Machine,
      Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent13CrossRouteHeldLeaf109.firstOneB0_1LC :=
  parentCoverWith12And16And17 B hB (BB6.Agent48Box12.box12_weighted B (by omega))
    bound16 bound17 hOpen

#print axioms parentCover29
#print axioms parentCover27
end BB6.Agent48Raw10RefinedBox12
