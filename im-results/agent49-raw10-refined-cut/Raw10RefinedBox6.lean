import Raw10RefinedBox7
import Box6SourceConsumer
import Raw10RefinedHeld

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent49Raw10RefinedBox6

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49BoxBridge
open BB6.Agent13CrossRouteHeldLeaf109 BB6.Agent49Raw10RefinedCut
open BB6.Agent50RootFrontier BB6.Agent49Box
open BB6.Agent49Raw10RefinedHeld

/-- Kernel-check that the sixth refined rectangle is accepted by Box6's source matcher. -/
theorem sourceIndex6 : BB6.Agent49Box6.sourceMatch raw10Remainder[6]! = true := by
  decide +kernel

/-- Transfer the source-accepted weighted bound through the exact source matcher. -/
theorem sourceBound6 (B : Nat) (hB : 75 ≤ B) (m : Machine)
    (hm : Fits raw10Remainder[6]! m) : WeightedBound B m :=
  BB6.Agent49Box6.box6_weighted B hB m
    (BB6.Agent49Box6.sourceMatch_sound _ sourceIndex6 m hm)

/-- Add the original-source Box6 rectangle to an already bounded cut. -/
def add6 (cs : List RBox) : List RBox := cs ++ [raw10Remainder[6]!]

theorem add6_bounds (B : Nat) (hB : 75 ≤ B) (cs : List RBox)
    (hc : ∀ r ∈ cs, ∀ m : Machine, Fits r m → WeightedBound B m) :
    ∀ r ∈ add6 cs, ∀ m : Machine, Fits r m → WeightedBound B m := by
  intro r hr m hm
  change r ∈ cs ++ [raw10Remainder[6]!] at hr
  rcases List.mem_append.mp hr with hs | ht
  · exact hc r hs m hm
  · have he : r = raw10Remainder[6]! := by simpa using ht
    subst r
    exact sourceBound6 B hB m hm

def acceptedWith6 : List RBox :=
  add6 (BB6.Agent49Raw10RefinedBox7.add7
    (BB6.Agent49Raw10RefinedBox5.add5 accepted))

def candidateWith6 : List RBox :=
  add6 (BB6.Agent49Raw10RefinedBox7.add7
    (BB6.Agent49Raw10RefinedBox5.add5 candidate))

theorem open30 : (openBoxes acceptedWith6).length = 30 := by decide +kernel
theorem open28 : (openBoxes candidateWith6).length = 28 := by decide +kernel

/-- Conditional Raw10 parent Cover after consuming original-source boxes 5, 6, and 7. -/
def parentCover30 (B : Nat) (hB : 7014 ≤ B)
    (hOpen : ∀ r ∈ openBoxes acceptedWith6, ∀ m : Machine,
      Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  parentCover B hB acceptedWith6 (held_weighted B)
    (add6_bounds B (by omega) _ (
      BB6.Agent49Raw10RefinedBox7.add7_bounds B (by omega)
        (BB6.Agent49Raw10RefinedBox5.add5 accepted)
        (BB6.Agent49Raw10RefinedBox5.add5_bounds B (by omega) accepted
          (accepted_bounds B hB))) ) hOpen

/-- Conditional candidate Cover when the separate box16/17 bounds are supplied. -/
def parentCover28 (B : Nat) (hB : 7376 ≤ B)
    (bound16 : ∀ m : Machine, Fits raw10Remainder[16]! m → WeightedBound 7376 m)
    (bound17 : ∀ m : Machine, Fits raw10Remainder[17]! m → WeightedBound 7014 m)
    (hOpen : ∀ r ∈ openBoxes candidateWith6, ∀ m : Machine,
      Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  parentCover B (by omega) candidateWith6 (held_weighted B)
    (add6_bounds B (by omega) _ (
      BB6.Agent49Raw10RefinedBox7.add7_bounds B (by omega)
        (BB6.Agent49Raw10RefinedBox5.add5 candidate)
        (BB6.Agent49Raw10RefinedBox5.add5_bounds B (by omega) candidate
          (candidate_bounds B hB bound16 bound17))) ) hOpen

#print axioms sourceIndex6
#print axioms open30
#print axioms open28
#print axioms parentCover30
#print axioms parentCover28

end BB6.Agent49Raw10RefinedBox6
