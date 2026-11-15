import TM63RootResidueSix
import M0EvenResidueFour
import M2OddGenericStage
import Lean.Elab.Tactic.Omega

/-!
# Candidate authentic-root extension through the M0-even residue-four and M2-odd rows

This module composes two existing parameterized original-TM2 increment
candidates with the current authentic blank-root endpoint after middle row 11.

The first row uses n=16*r+4=8*(2*r)+4, marker 0, via
`m0Even_residue4_counted_increment_source`.  The next row uses the resulting
odd n=16*r+3, marker 2, via the generic
`m2Odd_counted_increment_source`.

**Status:** integration candidate only.  The imported M0-even row and the
ordered root dependency closure have not yet passed a current local compile
and transitive `sorryAx` audit.  No new verified lower bound is claimed.
-/

namespace BB6Coverage.Agent8TM63RootResidueFour

open BB6ChampionArithmetic
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent48M0EvenResidueFour
open BB6Coverage.Agent42M2OddGeneric

set_option maxHeartbeats 3000000

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add,h1]
  simp only [Option.bind_some]
  exact h2

/-- The root index is exactly 16*r+15 at the middle-row-11 boundary. -/
theorem tm63_root_index_eq_16r15 :
    tm63Index1 = 16*tm63RootResidueSixK+15 := by
  calc
    tm63Index1 = 8*tm63RootMiddleK+7 := tm63_index1_eq_8k7
    _ = 8*(2*(tm63RootMiddleK/2)+1)+7 := by
      rw [tm63_root_middle_k_split]
    _ = 16*tm63RootResidueSixK+15 := by
      simp [tm63RootResidueSixK]
      omega

private theorem tm63_root_length_ge_three : 3 ≤ tm63Length1 := by
  have hA := tm63FirstSection_exponent_ge_five
  have hlen : tm63Length1 = tm63FirstSection.exponent+5 := by
    dsimp [tm63Length1]
    omega
  omega

private theorem tm63_root_residue4_bound :
    8*(2*tm63RootResidueSixK)+4 < 2^tm63Length1 := by
  have hroot := tm63_index1_lt_pow_length1
  rw [tm63_root_index_eq_16r15] at hroot
  omega

private theorem tm63_root_residue3_bound :
    16*tm63RootResidueSixK+3 < 2^tm63Length1 := by
  have hroot := tm63_index1_lt_pow_length1
  rw [tm63_root_index_eq_16r15] at hroot
  omega

private theorem tm63_middle_after11_a_pos :
    0 < tm63MiddleAfter11A := by
  simp [tm63MiddleAfter11A,nextExponent]
  omega

/-- Marker-0, n=16*r+4 source row appended to the genuine blank-root
endpoint after middle row 11.  This is a candidate composition until the
M0-even residue-four source closure is compiled and axiom-audited. -/
def tm63MiddleAfter12A : Nat :=
  tm63MiddleAfter11A+tm63MiddleAfter11B+1

def tm63MiddleAfter12B : Nat :=
  2^tm63MiddleAfter11B-1

def tm63MiddleAfter12Head : Int :=
  tm63MiddleAfter11Head+5+3*tm63MiddleAfter11B

def tm63MiddleFirst12Moves : Nat :=
  tm63MiddleFirst11Moves+
    proposedIncrementCost 0 (16*tm63RootResidueSixK+4)
      tm63MiddleAfter11A tm63MiddleAfter11B

theorem tm63_blank_reaches_after_middle12 :
    run tm2 tm63MiddleFirst12Moves blank =
      some (s1Config tm63Length1 (16*tm63RootResidueSixK+3) 2
        tm63MiddleAfter12A 0 tm63MiddleAfter12B tm63MiddleAfter12Head) := by
  have hrow := m0Even_residue4_counted_increment_source
    tm63Length1 (2*tm63RootResidueSixK)
    tm63MiddleAfter11A tm63MiddleAfter11B tm63MiddleAfter11Head
    tm63_root_length_ge_three tm63_root_residue4_bound
    tm63_middle_after11_a_pos
  have hrow' :
      run tm2
        (proposedIncrementCost 0 (16*tm63RootResidueSixK+4)
          tm63MiddleAfter11A tm63MiddleAfter11B)
        (s1Config tm63Length1 (16*tm63RootResidueSixK+4) 0
          tm63MiddleAfter11A 0 tm63MiddleAfter11B tm63MiddleAfter11Head) =
      some (s1Config tm63Length1 (16*tm63RootResidueSixK+3) 2
        tm63MiddleAfter12A 0 tm63MiddleAfter12B tm63MiddleAfter12Head) := by
    simpa [tm63MiddleAfter12A,tm63MiddleAfter12B,tm63MiddleAfter12Head,
      Nat.mul_assoc] using hrow
  exact run_compose_local tm63_blank_reaches_after_middle11 hrow'

#print axioms tm63_root_index_eq_16r15
#print axioms tm63_blank_reaches_after_middle12

/-- The next source row is an odd m=2 reset, covered by the generic
`m2Odd_counted_increment_source` theorem. -/
def tm63MiddleAfter13A : Nat :=
  nextExponent 2 tm63MiddleAfter12A tm63MiddleAfter12B

def tm63MiddleAfter13B : Nat :=
  nextRight tm63MiddleAfter12B

def tm63MiddleAfter13Head : Int :=
  tm63MiddleAfter12Head+5+3*tm63MiddleAfter12B

def tm63MiddleFirst13Moves : Nat :=
  tm63MiddleFirst12Moves+
    proposedIncrementCost 2 (16*tm63RootResidueSixK+3)
      tm63MiddleAfter12A tm63MiddleAfter12B

theorem tm63_blank_reaches_after_middle13 :
    run tm2 tm63MiddleFirst13Moves blank =
      some (s1Config tm63Length1 (16*tm63RootResidueSixK+2) 1
        tm63MiddleAfter13A 0 tm63MiddleAfter13B tm63MiddleAfter13Head) := by
  have hn : (16*tm63RootResidueSixK+3)%2=1 := by omega
  have hrow := m2Odd_counted_increment_source
    tm63Length1 (16*tm63RootResidueSixK+3)
    tm63MiddleAfter12A tm63MiddleAfter12B tm63MiddleAfter12Head
    hn tm63_root_residue3_bound
  have hrow' :
      run tm2
        (proposedIncrementCost 2 (16*tm63RootResidueSixK+3)
          tm63MiddleAfter12A tm63MiddleAfter12B)
        (s1Config tm63Length1 (16*tm63RootResidueSixK+3) 2
          tm63MiddleAfter12A 0 tm63MiddleAfter12B tm63MiddleAfter12Head) =
      some (s1Config tm63Length1 (16*tm63RootResidueSixK+2) 1
        tm63MiddleAfter13A 0 tm63MiddleAfter13B tm63MiddleAfter13Head) := by
    simpa [tm63MiddleAfter13A,tm63MiddleAfter13B,tm63MiddleAfter13Head,
      nextExponent,nextRight] using hrow
  exact run_compose_local tm63_blank_reaches_after_middle12 hrow'

#print axioms tm63_blank_reaches_after_middle13

end BB6Coverage.Agent8TM63RootResidueFour
