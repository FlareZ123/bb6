import TM63RootAfterSectionResultToOne
import OuterLCIncCanonicalEndpoint

/-!
# Compose the authentic TM63 root prefix with the marker-1 S0 endpoint

This module joins the existing source-level blank-root theorem through the
middle-34 rows and outer-LC_Inc nested frame to the pointwise canonical
marker-1 S0 tape identification.  It makes the right-counter terminal parameters explicit; the root-specific
lower bound needed for the positive-z q4 macro remains a separate obligation.  It is a source draft until its complete dependency
closure is compiled and its exported axiom profile is audited; it proves
neither halting nor the exact champion score.
-/

namespace BB6Coverage.Agent44TM63RootMarker1Endpoint

open BB6Coverage
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent44TM63RootMiddle34
open BB6Coverage.Agent48RootAfterSectionResult
open BB6Coverage.Agent42OuterLCInc
open BB6Coverage.Agent8S1Encoder

def middle34Result :=
  sectionResult (16*tm63RootResidueSixK-20) 1
    tm63MiddleAfter34A tm63MiddleAfter34B

def middle34Head : Int :=
  sectionHeadAfter (16*tm63RootResidueSixK-20)
    tm63MiddleAfter34B tm63MiddleAfter34Head

/--
The authentic blank TM63 trajectory reaches the canonical marker-1 S0
configuration after the middle-34 continuation, full SectionResult
dispatcher, and outer-LC_Inc reset prefix.  The resulting parameters are
A = middle34Result.exponent + middle34Result.right + 2,
z = 2^middle34Result.right - 1, and head = middle34Head + 3*right + 5.
-/
theorem tm63_blank_reaches_after_middle34_marker1_s0 :
    run tm2
      (tm63MiddleFirst34Moves + middle34Result.cost +
        (12*middle34Result.exponent + 8 + 63 +
          3*middle34Result.right))
      blank =
    some ⟨3, middle34Head + 3*middle34Result.right + 5,
      (s0Config
        (markerWord 1 ++ d0 ++ d1pow tm63Length1 ++ lh)
        (middle34Result.exponent + middle34Result.right + 2)
        (2^middle34Result.right - 1) 0
        (middle34Head + 3*middle34Result.right + 5)).tape⟩ := by
  have hroot := tm63_blank_reaches_after_middle34_reset_frame
  have hL : 0 < tm63Length1 := by
    have hL4 := tm63_root_length_ge_four
    omega
  have hcanonical := outerLCIncPostludeTape_eq_marker1S0_m2
    tm63Length1 middle34Result.exponent middle34Result.right
    middle34Head hL
  rw [hcanonical] at hroot
  simpa [middle34Result, middle34Head] using hroot

/-- The canonical marker-1 S0 width/value bounds needed by the positive-z
q4 terminal programme are inherited from the generic endpoint theorem. -/
theorem tm63_blank_reaches_after_middle34_marker1_s0_input_bounds :
    0 < middle34Result.exponent + middle34Result.right + 2 ∧
    2^middle34Result.right - 1 <
      2^(middle34Result.exponent + middle34Result.right + 2) :=
  outerLCInc_marker1S0_inputBounds
    middle34Result.exponent middle34Result.right

#print axioms tm63_blank_reaches_after_middle34_marker1_s0
#print axioms tm63_blank_reaches_after_middle34_marker1_s0_input_bounds

end BB6Coverage.Agent44TM63RootMarker1Endpoint
