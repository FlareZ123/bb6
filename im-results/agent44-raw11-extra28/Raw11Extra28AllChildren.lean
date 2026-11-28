import PhaseFrontier

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
An independent, exact 20-way original-source D1 parent split.

Unlike the earlier Raw11Extra28Refine, this consumes no precompiled sibling
Cover in its route: each of the twelve genuinely nontrivial children remains
a separate premise. This permits a source-level and proof-object-compatible
parent join once the already-discovered child certificates are accepted.
Eight siblings are discharged by the original translated-cycle checker.
-/

namespace BB6.Agent44Extra28AllChildren
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47PhaseFrontier

def parent : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true  => some (some ⟨false,false,3⟩)
  | _,_ => none

def route : Route 42 := BB6.Agent47PhaseFrontier.split 9 (3,true) 4 #[
  (.closed (.side 10 3 false (-2))),
  (.closed (.side 15 3 false (-1))),
  (.closed (.side 10 3 false (-2))),
  (.closed (.side 14 4 true (-2))),
  (.closed (.side 4 6 false 0)),
  (.closed (.side 1 12 false 2)),
  (.closed (.side 4 6 false 0)),
  .pending,
  .pending,
  .pending,
  .pending,
  (.closed (.side 2 8 false 2)),
  .pending,
  .pending,
  .pending,
  .pending,
  .pending,
  .pending,
  .pending,
  .pending
]

theorem checked : check 42 parent route = true := by decide +kernel

def remaining : List PartialMachine := residuals 42 parent route

theorem exactCodes :
    remaining.map tableCode =
      [26318896598422296, 26318896598879272, 26318896599336248,
       26318896599793224, 26318896600707176, 26318896601164152,
       26318896601621128, 26318896602078104, 26318896602535080,
       26318896602992056, 26318896603449032, 26318896603906008] := by
  decide +kernel

theorem exactly_twelve : remaining.length = 12 := by decide +kernel

theorem consume (B : Nat) (hB : 42 ≤ B)
    (hremaining : ∀ q ∈ remaining, ∀ m, compatible q m → WeightedBound B m) :
    Cover (WeightedBound B) parent :=
  .leaf _ (consumeAt 42 B hB parent route (by decide) checked hremaining)

#print axioms checked
#print axioms exactCodes
#print axioms consume
end BB6.Agent44Extra28AllChildren
