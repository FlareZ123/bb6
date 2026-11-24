import TM63RootAfterSectionResultToOne
import OuterLCIncCanonicalEndpoint

/-!
# Compose the authentic TM63 root prefix with the marker-1 S0 endpoint

This module joins the existing source-level blank-root theorem through the
middle-34 rows and outer-LC_Inc nested frame to the pointwise canonical
marker-1 S0 tape identification.  It makes the right-counter terminal parameters explicit and includes a
source-level proof that the authentic root has b ≥ 2 (hence z ≥ 3). The
complete dependency closure remains uncompiled.  It is a source draft until its complete dependency
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

/-- A reusable lower bound for the binary powers in the root B-counter chain. -/
private theorem root_pow2_ge_four (n : Nat) (hn : 2 ≤ n) : 4 ≤ 2^n := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  rw [hk, Nat.pow_add]
  rw [show (2:Nat)^2 = 4 by decide]
  have hp : 0 < 2^k := Nat.pow_pos (by decide)
  omega

private theorem root_nextRight_ge_two (b : Nat) (hb : 2 ≤ b) :
    2 ≤ nextRight b := by
  unfold nextRight
  have hp := root_pow2_ge_four b hb
  omega

private theorem root_pow2_sub_one_ge_two (b : Nat) (hb : 2 ≤ b) :
    2 ≤ 2^b - 1 := by
  have hp := root_pow2_ge_four b hb
  omega

private theorem root_sectionResult_right_ge_two
    (n m a b : Nat) (hb : 2 ≤ b) :
    2 ≤ (sectionResult n m a b).right := by
  induction n generalizing m a b with
  | zero =>
      simpa [sectionResult] using hb
  | succ n ih =>
      change 2 ≤
        (sectionResult n (nextMarker m) (nextExponent m a b)
          (nextRight b)).right
      exact ih (nextMarker m) (nextExponent m a b) (nextRight b)
        (root_nextRight_ge_two b hb)

private theorem root_middleAfter8B_ge_two
    (b : Nat) (hb : 2 ≤ b) :
    2 ≤ BB6Coverage.Agent42MiddleSectionCountdown.middleAfter8B b := by
  unfold BB6Coverage.Agent42MiddleSectionCountdown.middleAfter8B
    BB6Coverage.Agent42MiddleSectionCountdown.middleAfter7B
    BB6Coverage.Agent42MiddleSectionCountdown.middleAfter6B
    BB6Coverage.Agent42MiddleSectionCountdown.middleAfter5B
    BB6Coverage.Agent42MiddleSectionPrefix4.middleAfter4B
    BB6Coverage.Agent42MiddleSectionPrefix4.middleAfter3B
    BB6Coverage.Agent42MiddleSectionPrefix4.middleAfter2B
    BB6Coverage.Agent42MiddleSectionPrefix4.middleAfter1B
  repeat' apply root_nextRight_ge_two
  exact hb

/-- The authentic root's B-counter remains at least two through the
middle-34 handoff.  The proof follows the actual source recurrence from
the first-section right counter 63; every subsequent B update is either
`nextRight` or `2^b-1`, both preserving the lower bound. -/
theorem tm63MiddleAfter34B_ge_two :
    2 ≤ BB6Coverage.Agent44TM63RootMiddle34.tm63MiddleAfter34B := by
  have hfirst : 2 ≤ tm63FirstSection.right := by
    change 2 ≤ (sectionResult 7 2 6 63).right
    exact root_sectionResult_right_ge_two 7 2 6 63 (by decide)
  have h8 : 2 ≤ BB6Coverage.Agent42MiddleSectionCountdown.tm63MiddleAfter8B := by
    change 2 ≤
      BB6Coverage.Agent42MiddleSectionCountdown.middleAfter8B
        (nextRight tm63FirstSection.right)
    exact root_middleAfter8B_ge_two _ (root_nextRight_ge_two _ hfirst)
  have h9 : 2 ≤ BB6Coverage.Agent42RootResidueSix.tm63RootResidueSixB := by
    change 2 ≤
      2 ^ BB6Coverage.Agent42MiddleSectionCountdown.tm63MiddleAfter8B - 1
    exact root_pow2_sub_one_ge_two _ h8
  have h10 : 2 ≤ BB6Coverage.Agent42RootResidueSix.tm63MiddleAfter10B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent42RootResidueSix.tm63RootResidueSixB - 1
    exact root_pow2_sub_one_ge_two _ h9
  have h11 : 2 ≤ BB6Coverage.Agent42RootResidueSix.tm63MiddleAfter11B := by
    change 2 ≤ nextRight BB6Coverage.Agent42RootResidueSix.tm63MiddleAfter10B
    exact root_nextRight_ge_two _ h10
  have h12 : 2 ≤ BB6Coverage.Agent8TM63RootResidueFour.tm63MiddleAfter12B := by
    change 2 ≤ 2 ^ BB6Coverage.Agent42RootResidueSix.tm63MiddleAfter11B - 1
    exact root_pow2_sub_one_ge_two _ h11
  have h13 : 2 ≤ BB6Coverage.Agent8TM63RootResidueFour.tm63MiddleAfter13B := by
    change 2 ≤ nextRight BB6Coverage.Agent8TM63RootResidueFour.tm63MiddleAfter12B
    exact root_nextRight_ge_two _ h12
  have h14 : 2 ≤ BB6Coverage.Agent48TM63RootResidueTwo.tm63MiddleAfter14B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent8TM63RootResidueFour.tm63MiddleAfter13B - 1
    exact root_pow2_sub_one_ge_two _ h13
  have h15 : 2 ≤ BB6Coverage.Agent48TM63RootResidueThree.tm63MiddleAfter15B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent48TM63RootResidueTwo.tm63MiddleAfter14B - 1
    exact root_pow2_sub_one_ge_two _ h14
  have h16 : 2 ≤ BB6Coverage.Agent49TM63RootResidueSixteen.tm63MiddleAfter16B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent48TM63RootResidueThree.tm63MiddleAfter15B - 1
    exact root_pow2_sub_one_ge_two _ h15
  have h17 : 2 ≤ BB6Coverage.Agent49TM63RootResidueSixteen.tm63MiddleAfter17B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent49TM63RootResidueSixteen.tm63MiddleAfter16B - 1
    exact root_pow2_sub_one_ge_two _ h16
  have h18 : 2 ≤ BB6Coverage.Agent48TM63RootMiddle18.tm63MiddleAfter18B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent49TM63RootResidueSixteen.tm63MiddleAfter17B - 1
    exact root_pow2_sub_one_ge_two _ h17
  have h19 : 2 ≤ BB6Coverage.Agent48TM63RootMiddle19.tm63MiddleAfter19B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent48TM63RootMiddle18.tm63MiddleAfter18B - 1
    exact root_pow2_sub_one_ge_two _ h18
  have h20 : 2 ≤ BB6Coverage.Agent48TM63RootMiddle20.tm63MiddleAfter20B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent48TM63RootMiddle19.tm63MiddleAfter19B - 1
    exact root_pow2_sub_one_ge_two _ h19
  have h21 : 2 ≤ BB6Coverage.Agent48TM63RootMiddle21.tm63MiddleAfter21B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent48TM63RootMiddle20.tm63MiddleAfter20B - 1
    exact root_pow2_sub_one_ge_two _ h20
  have h22 : 2 ≤ BB6Coverage.Agent48TM63RootMiddle22.tm63MiddleAfter22B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent48TM63RootMiddle21.tm63MiddleAfter21B - 1
    exact root_pow2_sub_one_ge_two _ h21
  have h23 : 2 ≤ BB6Coverage.Agent48TM63RootMiddle23.tm63MiddleAfter23B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent48TM63RootMiddle22.tm63MiddleAfter22B - 1
    exact root_pow2_sub_one_ge_two _ h22
  have h24 : 2 ≤ BB6Coverage.Agent48TM63RootMiddle24.tm63MiddleAfter24B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent48TM63RootMiddle23.tm63MiddleAfter23B - 1
    exact root_pow2_sub_one_ge_two _ h23
  have h25 : 2 ≤ BB6Coverage.Agent42TM63RootMiddle25.tm63MiddleAfter25B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent48TM63RootMiddle24.tm63MiddleAfter24B - 1
    exact root_pow2_sub_one_ge_two _ h24
  have h26 : 2 ≤ BB6Coverage.Agent42TM63RootMiddle26.tm63MiddleAfter26B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent42TM63RootMiddle25.tm63MiddleAfter25B - 1
    exact root_pow2_sub_one_ge_two _ h25
  have h27 : 2 ≤ BB6Coverage.Agent44TM63RootMiddle34.tm63MiddleAfter27B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent42TM63RootMiddle26.tm63MiddleAfter26B - 1
    exact root_pow2_sub_one_ge_two _ h26
  have h28 : 2 ≤ BB6Coverage.Agent44TM63RootMiddle34.tm63MiddleAfter28B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent44TM63RootMiddle34.tm63MiddleAfter27B - 1
    exact root_pow2_sub_one_ge_two _ h27
  have h29 : 2 ≤ BB6Coverage.Agent44TM63RootMiddle34.tm63MiddleAfter29B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent44TM63RootMiddle34.tm63MiddleAfter28B - 1
    exact root_pow2_sub_one_ge_two _ h28
  have h30 : 2 ≤ BB6Coverage.Agent44TM63RootMiddle34.tm63MiddleAfter30B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent44TM63RootMiddle34.tm63MiddleAfter29B - 1
    exact root_pow2_sub_one_ge_two _ h29
  have h31 : 2 ≤ BB6Coverage.Agent44TM63RootMiddle34.tm63MiddleAfter31B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent44TM63RootMiddle34.tm63MiddleAfter30B - 1
    exact root_pow2_sub_one_ge_two _ h30
  have h32 : 2 ≤ BB6Coverage.Agent44TM63RootMiddle34.tm63MiddleAfter32B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent44TM63RootMiddle34.tm63MiddleAfter31B - 1
    exact root_pow2_sub_one_ge_two _ h31
  have h33 : 2 ≤ BB6Coverage.Agent44TM63RootMiddle34.tm63MiddleAfter33B := by
    change 2 ≤
      2 ^ BB6Coverage.Agent44TM63RootMiddle34.tm63MiddleAfter32B - 1
    exact root_pow2_sub_one_ge_two _ h32
  exact root_pow2_sub_one_ge_two _ h33

/-- The full SectionResult dispatcher preserves the root B-counter lower
bound, so the marker-1 S0 endpoint has a genuinely positive right counter. -/
theorem tm63Middle34Result_right_ge_two :
    2 ≤ middle34Result.right := by
  change 2 ≤
    (sectionResult (16*tm63RootResidueSixK-20) 1
      tm63MiddleAfter34A tm63MiddleAfter34B).right
  exact root_sectionResult_right_ge_two
    (16*tm63RootResidueSixK-20) 1
    tm63MiddleAfter34A tm63MiddleAfter34B
    tm63MiddleAfter34B_ge_two

/-- The authentic marker-1 S0 endpoint is in the positive-z branch:
(z=2^b-1\ge3). -/
theorem tm63Middle34Result_z_ge_three :
    3 ≤ 2^middle34Result.right - 1 := by
  have hp := root_pow2_ge_four middle34Result.right
    tm63Middle34Result_right_ge_two
  omega

#print axioms tm63_blank_reaches_after_middle34_marker1_s0
#print axioms tm63_blank_reaches_after_middle34_marker1_s0_input_bounds
#print axioms tm63MiddleAfter34B_ge_two
#print axioms tm63Middle34Result_right_ge_two
#print axioms tm63Middle34Result_z_ge_three

end BB6Coverage.Agent44TM63RootMarker1Endpoint
