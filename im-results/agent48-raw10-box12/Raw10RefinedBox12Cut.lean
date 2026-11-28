import Raw10RefinedBox6

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent48Raw10RefinedBox12Cut
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49BoxBridge
open BB6.Agent13CrossRouteHeldLeaf109 BB6.Agent49Raw10RefinedCut
open BB6.Agent50RootFrontier BB6.Agent49Box
open BB6.Agent49Raw10RefinedHeld BB6.Agent49Raw10RefinedBox6

def add12 (cs : List RBox) : List RBox := cs ++ [raw10Remainder[12]!]

theorem add12_bounds (B : Nat) (cs : List RBox)
    (h12 : ∀ m : Machine, Fits raw10Remainder[12]! m → WeightedBound B m)
    (hc : ∀ r ∈ cs, ∀ m : Machine, Fits r m → WeightedBound B m) :
    ∀ r ∈ add12 cs, ∀ m : Machine, Fits r m → WeightedBound B m := by
  intro r hr m hm
  change r ∈ cs ++ [raw10Remainder[12]!] at hr
  rcases List.mem_append.mp hr with hs | ht
  · exact hc r hs m hm
  · have he : r = raw10Remainder[12]! := by simpa using ht
    subst r
    exact h12 m hm

def acceptedWith12 : List RBox := add12 acceptedWith6
def candidateWith12 : List RBox := add12 candidateWith6

theorem open29 : (openBoxes acceptedWith12).length = 29 := by decide +kernel
theorem open27 : (openBoxes candidateWith12).length = 27 := by decide +kernel

theorem parentCoverWith12 (B : Nat) (hB : 7014 ≤ B)
    (h12 : ∀ m : Machine, Fits raw10Remainder[12]! m → WeightedBound B m)
    (hOpen : ∀ r ∈ openBoxes acceptedWith12, ∀ m : Machine,
      Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  parentCover B hB acceptedWith12 (held_weighted B)
    (add12_bounds B _ h12 (add6_bounds B (by omega) _
      (BB6.Agent49Raw10RefinedBox7.add7_bounds B (by omega)
        (BB6.Agent49Raw10RefinedBox5.add5 accepted)
        (BB6.Agent49Raw10RefinedBox5.add5_bounds B (by omega) accepted
          (accepted_bounds B hB))))) hOpen

theorem parentCoverWith12And16And17 (B : Nat) (hB : 7376 ≤ B)
    (h12 : ∀ m : Machine, Fits raw10Remainder[12]! m → WeightedBound B m)
    (bound16 : ∀ m : Machine, Fits raw10Remainder[16]! m → WeightedBound 7376 m)
    (bound17 : ∀ m : Machine, Fits raw10Remainder[17]! m → WeightedBound 7014 m)
    (hOpen : ∀ r ∈ openBoxes candidateWith12, ∀ m : Machine,
      Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  parentCover B (by omega) candidateWith12 (held_weighted B)
    (add12_bounds B _ h12 (add6_bounds B (by omega) _
      (BB6.Agent49Raw10RefinedBox7.add7_bounds B (by omega)
        (BB6.Agent49Raw10RefinedBox5.add5 candidate)
        (BB6.Agent49Raw10RefinedBox5.add5_bounds B (by omega) candidate
          (candidate_bounds B hB bound16 bound17))))) hOpen

#print axioms open29
#print axioms open27
#print axioms parentCoverWith12
#print axioms parentCoverWith12And16And17
end BB6.Agent48Raw10RefinedBox12Cut
