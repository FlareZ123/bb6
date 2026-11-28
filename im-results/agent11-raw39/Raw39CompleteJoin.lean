import Raw39ExactJoin
import Raw390LEComplete
import Raw391LEComplete

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
This is the final *source-level candidate* joining the two generated complete
LE child bounds to the nine already source-accepted siblings. It is not
accepted as a theorem until the complete exact source/object dependency closure
has been compiled and audited with Lean 4.36.0-rc2.
-/

namespace BB6.Agent11Raw39Closed

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent11SemanticChunks
open BB6.Agent10ZipAudit
open BB6.Agent11Raw39AcceptedSix (p39 child)

theorem zeroLE_bound : Bound 15125 (child ⟨false,false,4⟩) := by
  exact BB6.Agent11Raw390LE.all0LE

theorem oneLE_bound : Bound 28311 (child ⟨true,false,4⟩) := by
  exact BB6.Agent11Raw391LE.all1LE

theorem parent_bound : Bound 28311 p39 :=
  BB6.Agent43Raw39ExactJoin.parent_bound zeroLE_bound oneLE_bound

theorem parent_cover : Cover (WeightedBound 28311) p39 :=
  BB6.Agent43Raw39ExactJoin.parent_cover zeroLE_bound oneLE_bound

theorem parent_exact (B : Nat) : Bound B p39 ↔ 28311 ≤ B :=
  BB6.Agent43Raw39ExactJoin.parent_exact zeroLE_bound oneLE_bound B

theorem parent_attained :
    ∃ m k d, compatible p39 m ∧ HaltsAfter m k ∧
      d ∈ delays (zeroNext m) 0 ∧ d+k+1 = 28311 :=
  BB6.Agent43Raw39ExactJoin.parent_attained

#print axioms zeroLE_bound
#print axioms oneLE_bound
#print axioms parent_bound
#print axioms parent_cover
#print axioms parent_exact
#print axioms parent_attained

end BB6.Agent11Raw39Closed
