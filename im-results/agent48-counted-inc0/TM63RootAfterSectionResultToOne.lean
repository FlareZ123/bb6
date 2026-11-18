import TM63RootMiddle34
import TM63SourceIncrementDispatcherComplete
import Lean.Elab.Tactic.Omega

/-!
# Authentic root continuation to the final index-one reset input

The middle-34 blank-root theorem is composed with the complete 24-class
SectionResult dispatcher, stopping at index one rather than zero. The
first-section parity fixes the root residue modulo three, so the remaining
marker is exactly 2. This is the natural input to the m=2, n=1 reset-base
family. The arbitrary-a,b reset-prefix and exact terminal S0 embedding are
still separate obligations.
-/

namespace BB6Coverage.Agent48RootAfterSectionResult

open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent44TM63RootMiddle34
open BB6Coverage.Agent44SectionResultRunSource
open BB6Coverage.Agent24ChampionTime
open BB6ChampionArithmetic

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add,h1]
  simp only [Option.bind_some]
  exact h2

private theorem pow_two_even_mod_three (k : Nat) :
    (2^(2*k)) % 3 = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      calc
        (2^(2*(k+1))) % 3 = (2^(2*k+2)) % 3 := by
          congr 1 <;> omega
        _ = (2^(2*k) * 2^2) % 3 := by
          rw [Nat.pow_add]
        _ = ((2^(2*k) % 3) * (2^2 % 3)) % 3 := by
          rw [Nat.mul_mod]
        _ = 1 := by norm_num [ih]

private theorem pow_two_mod_three_of_even (n : Nat)
    (hn : n % 2 = 0) : (2^n) % 3 = 1 := by
  have hdiv : 2 ∣ n := by omega
  rcases hdiv with ⟨k, hk⟩
  simpa [hk] using pow_two_even_mod_three k

/-- The actual root middle quotient is divisible by three. -/
theorem tm63_root_middle_k_mod_three :
    tm63RootMiddleK % 3 = 0 := by
  have hA : 5 ≤ tm63FirstSection.exponent :=
    tm63FirstSection_exponent_ge_five
  have hAodd : tm63FirstSection.exponent % 2 = 1 := by
    simpa [tm63FirstSection] using first_stage_exponent_odd
  have heven : (tm63FirstSection.exponent-3) % 2 = 0 := by omega
  have hpow := pow_two_mod_three_of_even
    (tm63FirstSection.exponent-3) heven
  have hprod :
      (31*2^(tm63FirstSection.exponent-3)) % 3 = 1 := by
    rw [Nat.mul_mod]
    norm_num [hpow]
  unfold tm63RootMiddleK
  omega

/-- The half-quotient used by the middle-34 itinerary is 1 modulo 3. -/
theorem tm63_root_residue_six_k_mod_three :
    tm63RootResidueSixK % 3 = 1 := by
  have hsplit : tm63RootMiddleK = 2*tm63RootResidueSixK+1 := by
    simpa [tm63RootResidueSixK] using tm63_root_middle_k_split
  have hK := tm63_root_middle_k_mod_three
  rw [hsplit] at hK
  omega

/-- At the authentic middle-34 input, all but the final decrement leaves
index one and marker two. -/
theorem tm63_middle34_sectionResult_marker_two :
    (sectionResult (16*tm63RootResidueSixK-20) 1
      tm63MiddleAfter34A tm63MiddleAfter34B).marker = 2 := by
  rw [sectionResult_marker]
  have hr := tm63_root_residue_six_k_mod_three
  omega

/-- The blank-root TM63 run reaches the exact S1 state with index one and
marker two after the complete source-checked SectionResult prefix. -/
theorem tm63_blank_reaches_after_middle34_to_index_one :
    run tm2
      (tm63MiddleFirst34Moves +
        (sectionResult (16*tm63RootResidueSixK-20) 1
          tm63MiddleAfter34A tm63MiddleAfter34B).cost)
      blank =
    some (s1Config tm63Length1 1 2
      (sectionResult (16*tm63RootResidueSixK-20) 1
        tm63MiddleAfter34A tm63MiddleAfter34B).exponent
      0
      (sectionResult (16*tm63RootResidueSixK-20) 1
        tm63MiddleAfter34A tm63MiddleAfter34B).right
      (sectionHeadAfter (16*tm63RootResidueSixK-20)
        tm63MiddleAfter34B tm63MiddleAfter34Head)) := by
  have hroot := tm63_blank_reaches_after_middle34
  have hL : 4 ≤ tm63Length1 := tm63_root_length_ge_four
  have hindex : tm63Index1 =
      16*tm63RootResidueSixK+15 := tm63_index1_eq_16k15
  have hrootBound := tm63_index1_lt_pow_length1
  rw [hindex] at hrootBound
  have hbound : 16*tm63RootResidueSixK-19 < 2^tm63Length1 := by
    omega
  have ha : 0 < tm63MiddleAfter34A := by
    unfold tm63MiddleAfter34A
    omega
  have hsection := sectionResult_run_to_index_one_complete
    tm63Length1 (16*tm63RootResidueSixK-20) 1
    tm63MiddleAfter34A tm63MiddleAfter34B tm63MiddleAfter34Head
    hL (by omega) ha
  have hcomp := run_compose_local hroot hsection
  have hmarker := tm63_middle34_sectionResult_marker_two
  simpa [hmarker] using hcomp

#print axioms tm63_root_middle_k_mod_three
#print axioms tm63_root_residue_six_k_mod_three
#print axioms tm63_middle34_sectionResult_marker_two
#print axioms tm63_blank_reaches_after_middle34_to_index_one

end BB6Coverage.Agent48RootAfterSectionResult
