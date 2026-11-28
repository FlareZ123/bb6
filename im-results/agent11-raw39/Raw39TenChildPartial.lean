import Raw39ExactJoin
import Raw390LEComplete

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
All source-accepted first-hole branches except 1LE are consumed together.
The only hypothesis is the *entire* remaining 1LE child weighted bound.
This is a partial parent and not the accepted full Raw39 bound.
-/
namespace BB6.Agent11Raw39TenChild

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent11SemanticChunks
open BB6.Agent11Raw39AcceptedSix (p39 child)

theorem zeroLE_bound : Bound 15125 (child ⟨false,false,4⟩) :=
  BB6.Agent11Raw390LE.all0LE

theorem conditional_parent_bound
    (h : Bound 28311 (child ⟨true,false,4⟩)) : Bound 28311 p39 :=
  BB6.Agent43Raw39ExactJoin.parent_bound zeroLE_bound h

theorem conditional_parent_cover
    (h : Bound 28311 (child ⟨true,false,4⟩)) :
    Cover (WeightedBound 28311) p39 :=
  BB6.Agent43Raw39ExactJoin.parent_cover zeroLE_bound h

theorem conditional_parent_exact
    (h : Bound 28311 (child ⟨true,false,4⟩)) (B : Nat) :
    Bound B p39 ↔ 28311 ≤ B :=
  BB6.Agent43Raw39ExactJoin.parent_exact zeroLE_bound h B

#print axioms zeroLE_bound
#print axioms conditional_parent_bound
#print axioms conditional_parent_cover
#print axioms conditional_parent_exact
end BB6.Agent11Raw39TenChild
