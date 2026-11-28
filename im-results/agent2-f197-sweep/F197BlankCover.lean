import RootTheorem
import F197WeightedLeaf

namespace F197.CoverBridge
open BB6Coverage (Cover)
open BB6.Agent13BlankDelay (WeightedBound)

/-- Once the genuine blank stream run is proved live, *every* complete
    original six-state machine extending the literal F197 table is
    bounded, at every finite score, because it never halts.  The only
    missing row C1 is universally quantified by compatible. -/
theorem blank_cover (B : Nat) : Cover (WeightedBound B) table :=
  weighted_leaf B F197.Agent2Self.blank_nonhalt

#print axioms blank_cover
end F197.CoverBridge
