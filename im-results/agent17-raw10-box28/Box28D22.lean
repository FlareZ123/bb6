import Box28Symmetry
import Box28D18Closure

namespace BB6.Agent17.Box28D22
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode slot)
open BB6.Agent17.Box28Symmetry

/-- The exact D1=22 sibling inherits the accepted D1=18 weighted bound. -/
theorem sourceBound : ∀ m, Fits (sourceCut 22) m → WeightedBound 3640 m :=
  transportFor 14 22 (fun m hm => BB6.Agent13.Box28D18.sourceBound m hm)

theorem parentCutBound (m : Machine) (hm : Fits raw10Remainder[28]! m)
    (h0 : m (slot 6) = decode 14) (h1 : m (slot 7) = decode 22) :
    WeightedBound 3640 m :=
  sourceBound m (sourceCut_fits 22 m hm h0 h1)

#print axioms sourceBound
#print axioms parentCutBound
end BB6.Agent17.Box28D22
