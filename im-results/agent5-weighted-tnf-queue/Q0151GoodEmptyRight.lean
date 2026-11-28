import Q0151FiniteCertificate
import Q0151CEndPhysicalBridge

set_option maxHeartbeats 0

/-!
Kernel-certified abstract-to-physical side condition for the otherwise
delicate C-mode empty-right original-machine transition. If an 814-state
Good control is in C mode and its real right tape is blank, then the
current segment's last one-run category MUST be 3. Otherwise the exact
finite delta interpreter would generate its .bad action, contradicting
the verified all-actions-safe closure theorem.

Combined with the unbounded physical Scan normal-form theorem
c_end_trim_exact, this recovers the precise three trailing physical
one-bits necessary for the original C-end macro. No numeric search
bounds or extra assumptions on the length of the segment occur.
-/

namespace BB6.Agent5Q0151GoodEmptyRight
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151FiniteCertificate
open BB6.Agent5Q0151StackSaturation
open BB6.Agent5Q0151CEndPhysicalBridge

theorem good_no_bad (c : Control) (hc : Good c) :
    Action.bad ∉ delta c := by
  intro h
  have hs := finite_closed c hc Action.bad h
  exact hs

theorem c_blank_bad (s : SegmentSummary) (h : s.last ≠ 3) :
    Action.bad ∈ delta (mkControl false emptyRight s) := by
  simp [delta,actionsFor,choicesA,cut,emptyRight,mkControl,h]

theorem good_c_blank_last_three (s : SegmentSummary)
    (hc : Good (mkControl false emptyRight s)) :
    s.last = 3 := by
  by_contra h
  exact good_no_bad _ hc (c_blank_bad s h)

theorem good_c_blank_physical_trim (s : List Bool)
    (hs : BB6.Agent5Q0151SegmentGrammar.SegGood s)
    (hc : Good (mkControl false emptyRight
      (segAppend emptySegment s))) :
    ∃ pref : List Bool,
      s = pref ++ [true] ∧
      BB6.Agent5Q0151SegmentGrammar.SegGood pref ∧
      segAppend emptySegment pref =
        {segAppend emptySegment s with last := 2} := by
  exact c_end_trim_exact s hs
    (good_c_blank_last_three _ hc)

#print axioms good_no_bad
#print axioms good_c_blank_last_three
#print axioms good_c_blank_physical_trim
end BB6.Agent5Q0151GoodEmptyRight
