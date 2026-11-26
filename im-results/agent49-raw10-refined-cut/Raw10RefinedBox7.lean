import Raw10RefinedBox5
import Box7SourceConsumer

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent49Raw10RefinedBox7
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49BoxBridge
open BB6.Agent13CrossRouteHeldLeaf109 BB6.Agent49Raw10RefinedCut
open BB6.Agent49Raw10RefinedBox5 BB6.Agent50RootFrontier BB6.Agent49Box

theorem sourceIndex7 : BB6.Agent49Box7.sourceMatch raw10Remainder[7]! = true := by
  decide +kernel

theorem sourceBound7 (B : Nat) (hB : 41 ≤ B) (m : Machine)
    (hm : Fits raw10Remainder[7]! m) : WeightedBound B m :=
  BB6.Agent49Box7.box7_weighted B hB m
    (BB6.Agent49Box7.sourceMatch_sound _ sourceIndex7 m hm)

def add7 (cs : List RBox) : List RBox := cs ++ [raw10Remainder[7]!]

theorem add7_bounds (B : Nat) (hB : 41 ≤ B) (cs : List RBox)
    (hc : ∀ r ∈ cs, ∀ m : Machine, Fits r m → WeightedBound B m) :
    ∀ r ∈ add7 cs, ∀ m : Machine, Fits r m → WeightedBound B m := by
  intro r hr m hm
  change r ∈ cs ++ [raw10Remainder[7]!] at hr
  rcases List.mem_append.mp hr with hs | ht
  · exact hc r hs m hm
  · have he : r = raw10Remainder[7]! := by simpa using ht
    subst r
    exact sourceBound7 B hB m hm

theorem open31 : (openBoxes (add7 (add5 accepted))).length = 31 := by decide +kernel
theorem open29 : (openBoxes (add7 (add5 candidate))).length = 29 := by decide +kernel

def parentCover31 (B : Nat) (hB : 7014 ≤ B)
    (hOpen : ∀ r ∈ openBoxes (add7 (add5 accepted)), ∀ m : Machine, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  parentCover B hB (add7 (add5 accepted)) (BB6.Agent49Raw10RefinedHeld.held_weighted B)
    (add7_bounds B (by omega) _ (add5_bounds B (by omega) accepted (accepted_bounds B hB))) hOpen

def parentCover29 (B : Nat) (hB : 7376 ≤ B)
    (bound16 : ∀ m : Machine, Fits raw10Remainder[16]! m → WeightedBound 7376 m)
    (bound17 : ∀ m : Machine, Fits raw10Remainder[17]! m → WeightedBound 7014 m)
    (hOpen : ∀ r ∈ openBoxes (add7 (add5 candidate)), ∀ m : Machine, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  parentCover B (by omega) (add7 (add5 candidate)) (BB6.Agent49Raw10RefinedHeld.held_weighted B)
    (add7_bounds B (by omega) _ (add5_bounds B (by omega) candidate (candidate_bounds B hB bound16 bound17))) hOpen

#print axioms sourceIndex7
#print axioms sourceBound7
#print axioms open31
#print axioms open29
#print axioms parentCover31
#print axioms parentCover29
end BB6.Agent49Raw10RefinedBox7
