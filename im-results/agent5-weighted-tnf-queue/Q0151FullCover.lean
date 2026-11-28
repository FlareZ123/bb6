import Q0151RegionLift
import Q0151SourceActions4
import Q0151SourceActions5
import Q0151SourceActions6
import Q0151SourceActions7
import Q0151SourceActions8
import Q0151SourceActions9
import Q0151SourceActions10
import Q0151SourceActions11
import Q0151SourceActions12
import Q0151PackedLiveness
import Q0151RunLengthCases
import WeightedTNF

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
q0-151 original-source nonhalting proof target.
The 814-control kernel finite invariant, source-machine all-length
primitive macros, literal physical marker stack, abstract stay/push/pop
refinement, live-run arithmetical exhaustiveness, and empty-stack
zero-padding are combined into one self-reproducing original-machine
region. No bounded simulation or assumed macro step is used.

To accept this result the exact full Lean transitive dependency graph
must compile with #print axioms cover showing no sorryAx. This file
makes no statement about BB(6) global maximality.
-/

namespace BB6.Agent5Q0151FullCover
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151PhysicalStack
open BB6.Agent5Q0151SourceActions1
open BB6.Agent5Q0151SourceActions3
open BB6.Agent5Q0151SourceActions4
open BB6.Agent5Q0151SourceActions5
open BB6.Agent5Q0151SourceActions6
open BB6.Agent5Q0151SourceActions7
open BB6.Agent5Q0151SourceActions8
open BB6.Agent5Q0151SourceActions9
open BB6.Agent5Q0151SourceActions10
open BB6.Agent5Q0151SourceActions11
open BB6.Agent5Q0151SourceActions12
open BB6.Agent5Q0151RegionLift
open BB6.Agent5Q0151GoodEmptyRight
open BB6.Agent5Q0151B2AllowedSecond
open BB6.Agent5Q0151RunLengthCases
open BB6.Agent5Q0151SegmentGrammar
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151RightWordsComplete
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151FiniteCertificate
open BB6.Agent5Q0151PackedLiveness

theorem progress_b (s : List Bool) (st : List (List Bool))
    (rs : List Nat) (hs : SegGood s) (hst : StackOK st)
    (hc : Good (co true s rs)) :
    ∃ y, Region y ∧ Goes (boundary 1 s st (runBits rs)) y := by
  cases rs with
  | nil =>
      obtain ⟨decoded,ha,hg,hr⟩ := b_end_refines s hs st
      exact pop_step hc hst ha hg hr
  | cons n rest =>
      have hlive : rightType (rightSig (n::rest)) ≠ 0 :=
        good_live_right (co true s (n::rest)) hc
      rcases right_live_length_cases n rest hlive with
        h1 | h2 | h4 | h5 | h6
      · subst n
        obtain ⟨ha,hg⟩ := b_one_refines s st rest hlive
        exact stay_step hc hst (good_append_odd_one s hs) ha hg
      · subst n
        cases rest with
        | nil =>
            obtain ⟨decoded,ha,hg,hr⟩ := b_two_end_refines s hs st
            exact pop_step hc hst ha hg hr
        | cons m tail =>
            rcases b_two_second_allowed m tail hlive with hm4 | hm5
            · have hindex : ∃ k, m = 4*k+3 := by
                refine ⟨(m+1)/4-1,?_⟩
                omega
              obtain ⟨k,hk⟩ := hindex
              subst m
              obtain ⟨ha,hg⟩ := b_two_zero_refines k s st tail hlive
              exact stay_step hc hst
                (good_append_two_zero s hs (2*k+1)) ha hg
            · by_cases hm1 : m = 0
              · subst m
                obtain ⟨decoded,ha,hg,hr⟩ :=
                  b_two_one_refines s hs st tail hlive
                exact pop_step hc hst ha hg hr
              · have hindex : ∃ k, m = 4*k+4 := by
                  refine ⟨(m+1)/4-1,?_⟩
                  omega
                obtain ⟨k,hk⟩ := hindex
                subst m
                obtain ⟨decoded,ha,hg,hr⟩ :=
                  b_two_big_one_refines k s hs st tail hlive
                exact pop_step hc hst ha hg hr
      · obtain ⟨k,hk⟩ := h4
        have hn : n = 4*k+3 := by omega
        subst n
        obtain ⟨ha,hg⟩ := BB6.Agent5Q0151SourceActions10.b_four_refines k s st rest hlive
        exact push_step hc hs hst (good_alt_three (2*k)) ha hg
      · obtain ⟨k,hk⟩ := h5
        have hn : n = 4*k+4 := by omega
        subst n
        obtain ⟨ha,hg⟩ := BB6.Agent5Q0151SourceActions10.b_five_refines k s st rest hlive
        exact push_step hc hs hst (good_alt_two (2*k+1)) ha hg
      · obtain ⟨k,hk⟩ := h6
        have hn : n = 4*k+5 := by omega
        subst n
        obtain ⟨decoded,ha,hg⟩ := BB6.Agent5Q0151SourceActions11.b_six_refines k s st rest hlive
        exact stay_step hc hst (good_append_four s hs) ha hg

theorem progress_c (s : List Bool) (st : List (List Bool))
    (rs : List Nat) (hs : SegGood s) (hst : StackOK st)
    (hc : Good (co false s rs)) :
    ∃ y, Region y ∧ Goes (boundary 2 s st (runBits rs)) y := by
  cases rs with
  | nil =>
      have hc' : Good
          (mkControl false emptyRight (segAppend emptySegment s)) := by
        simpa [co,mkControl,rightSig] using hc
      have hthree := good_c_blank_last_three (segAppend emptySegment s) hc'
      obtain ⟨decoded,ha,hg,hr⟩ := c_end_refines s hs hthree st
      exact pop_step hc hst ha hg hr
  | cons n rest =>
      have hlive : rightType (rightSig (n::rest)) ≠ 0 :=
        good_live_right (co false s (n::rest)) hc
      rcases right_live_length_cases n rest hlive with
        h1 | h2 | h4 | h5 | h6
      · subst n
        obtain ⟨ha,hg⟩ := c_one_refines s st rest hlive
        exact stay_step hc hst (good_append hs good_ones_two) ha hg
      · subst n
        obtain ⟨decoded,ha,hg,hr⟩ := c_two_refines s hs st rest hlive
        exact pop_step hc hst ha hg hr
      · obtain ⟨k,hk⟩ := h4
        have hn : n = 4*k+3 := by omega
        subst n
        obtain ⟨ha,hg⟩ := BB6.Agent5Q0151SourceActions10.c_four_refines k s st rest hlive
        exact stay_step hc hst (good_append_alt_three s hs (2*k+1)) ha hg
      · obtain ⟨k,hk⟩ := h5
        have hn : n = 4*k+4 := by omega
        subst n
        obtain ⟨ha,hg⟩ := BB6.Agent5Q0151SourceActions10.c_five_refines k s st rest hlive
        exact stay_step hc hst (good_append_alt_two s hs (2*k+2)) ha hg
      · obtain ⟨k,hk⟩ := h6
        have hn : n = 4*k+5 := by omega
        subst n
        obtain ⟨decoded,ha,hg,hr⟩ := BB6.Agent5Q0151SourceActions11.c_six_refines k s hs st rest hlive
        exact pop_step hc hst ha hg hr

theorem physical_progress (x : P) (hx : Region x) :
    ∃ y, Region y ∧ Goes x y := by
  obtain ⟨b,s,st,rs,he,hs,hst,hc⟩ := hx
  subst x
  cases b with
  | false =>
      simpa [srcQ] using progress_c s st rs hs hst hc
  | true =>
      simpa [srcQ] using progress_b s st rs hs hst hc

theorem never_cover : Cover NeverHalts p := by
  exact cover_of_region Region 1 (boundary 1 [true] [] [])
    blank_seed initial physical_progress

abbrev table : PartialMachine := p

/-! Exact one-hole Cover consumable by the weighted Raw11 q0 parent tree. -/
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf p (fun m hm => weighted_never B m (never_cover.sound m hm))

#print axioms progress_b
#print axioms progress_c
#print axioms physical_progress
#print axioms never_cover
#print axioms cover
end BB6.Agent5Q0151FullCover
