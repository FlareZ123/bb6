import Raw10RefinedHeld
import Box5SourceConsumer

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent49Raw10RefinedBox5
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49BoxBridge
open BB6.Agent13CrossRouteHeldLeaf109 BB6.Agent49Raw10RefinedCut
open BB6.Agent50RootFrontier BB6.Agent49Box

/-- The accepted exact Box5 bound composes with any list of source rectangles. -/
def add5 (cs : List RBox) : List RBox := cs ++ [raw10Remainder[5]!]

theorem add5_bounds (B : Nat) (hB : 160 ≤ B) (cs : List RBox)
    (hc : ∀ r ∈ cs, ∀ m : Machine, Fits r m → WeightedBound B m) :
    ∀ r ∈ add5 cs, ∀ m : Machine, Fits r m → WeightedBound B m := by
  intro r hr m hm
  change r ∈ cs ++ [raw10Remainder[5]!] at hr
  rcases List.mem_append.mp hr with hs | ht
  · exact hc r hs m hm
  · have he : r = raw10Remainder[5]! := by simpa using ht
    subst r
    intro k d hk hd
    exact Nat.le_trans (BB6.Agent49Box5.sourceBound m hm k d hk hd) hB

theorem open32 : (openBoxes (add5 accepted)).length = 32 := by decide +kernel
theorem open30 : (openBoxes (add5 candidate)).length = 30 := by decide +kernel

def parentCover32 (B : Nat) (hB : 7014 ≤ B)
    (hOpen : ∀ r ∈ openBoxes (add5 accepted), ∀ m : Machine, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  parentCover B hB (add5 accepted) (BB6.Agent49Raw10RefinedHeld.held_weighted B)
    (add5_bounds B (by omega) accepted (accepted_bounds B hB)) hOpen

def parentCover30 (B : Nat) (hB : 7376 ≤ B)
    (bound16 : ∀ m : Machine, Fits raw10Remainder[16]! m → WeightedBound 7376 m)
    (bound17 : ∀ m : Machine, Fits raw10Remainder[17]! m → WeightedBound 7014 m)
    (hOpen : ∀ r ∈ openBoxes (add5 candidate), ∀ m : Machine, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  parentCover B (by omega) (add5 candidate) (BB6.Agent49Raw10RefinedHeld.held_weighted B)
    (add5_bounds B (by omega) candidate (candidate_bounds B hB bound16 bound17)) hOpen

#print axioms open32
#print axioms open30
#print axioms parentCover32
#print axioms parentCover30
end BB6.Agent49Raw10RefinedBox5
