import WeightedTNFBridge
import FreshRayGlider

namespace BB6.Agent13BlankDelay
open BB6Coverage

/-- The four-step fresh-cell glider has a one-state FAR invariant. This
    executable search is only a candidate generator; the theorem below is
    checked by Lean and then consumed by the weighted-TNF adapter. -/
theorem gliderFAROracle : FAR.fastOracle gliderExample 2 = true := by
  decide

/-- A concrete weighted-TNF nonhalting leaf obtained from the FAR checker. -/
def gliderFARTNFLeaf (B : Nat) : WeightedTNFCertificate B gliderExample 3 :=
  farNonhaltLeaf
    (B := B) (p := gliderExample) (cut := 3)
    (by decide)
    (by decide)
    (by decide)
    2 gliderFAROracle

#print axioms gliderFAROracle
#print axioms gliderFARTNFLeaf
end BB6.Agent13BlankDelay
