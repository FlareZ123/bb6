import Q0151FiniteCertificate
import Q0151RightWordsComplete
import Q0151ParamSaturation

set_option maxHeartbeats 0

/-!
Universal linkage between the q0-151 finite closure and all-length physical
words. The generated 814-control proof computes Good, not a property of
concrete machine configurations. Here we derive the two properties of
Good required by a future original-source simulation:
(1) the actual first run of any concretely represented right tape is
    included in the model's next-run cut;
(2) every alternating-run parameter > 0 collapses to one abstract action,
    even when the current segment is an arbitrary Good control.
These conclusions are consequences of machine-independent concrete-word
lemmas plus the complete finite Good enumeration.
-/

namespace BB6.Agent5Q0151AbstractConcreteBridge
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151FiniteCertificate
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151RightWordsComplete
open BB6.Agent5Q0151ParamSaturation

theorem good_cut_real (c : Control) (hc : Good c)
    (xs : List Nat) (h : c.right = rightSig xs) :
    actualNext xs ∈ cut c.right := by
  have hs : rightType (rightSig xs) ≠ 0 := by
    rw [← h]
    exact good_live_right c hc
  have hh : actualNext xs ∈ cut (rightSig xs) :=
    cut_real_next xs hs
  rw [h]
  exact hh

theorem good_current_alt_positive (c : Control) (hc : Good c)
    (n : Nat) (hn : 0 < n) (tail : List Bool) :
    segAppend c.segment (altWord n ++ tail) =
      segAppend c.segment (altWord 1 ++ tail) := by
  have hi := good_segment_lower c hc
  exact alt_positive c.segment n hn tail hi.1 hi.2

theorem saved_alt_positive (s : SegmentSummary) (hs : s ∈ savedSegments)
    (n : Nat) (hn : 0 < n) (tail : List Bool) :
    segAppend s (altWord n ++ tail) =
      segAppend s (altWord 1 ++ tail) := by
  have hi := saved_segment_lower s hs
  exact alt_positive s n hn tail hi.1 hi.2

theorem good_right_not_zero (c : Control) (hc : Good c) :
    rightType c.right ≠ 0 :=
  good_live_right c hc

#print axioms good_cut_real
#print axioms good_current_alt_positive
#print axioms saved_alt_positive
end BB6.Agent5Q0151AbstractConcreteBridge
