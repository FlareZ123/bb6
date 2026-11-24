import TM63RootResidueSeven
import M2EvenSixGenericCounted
import M1OddResidueFive
import Lean.Elab.Tactic.Omega

/-!
# Blank-root TM63 countdown through the m=2,n=16*r+6 and m=1,n=16*r+5 rows

The first nine rows are supplied by the root-specific residue-seven
composition.  This module appends the quantified residue-six m=2 reset,
its counted drain, and the existing m=1 residue-five counted increment.
The result is an exact original-table blank-root run through eleven
middle-section increments.  It is still only a prefix of the full
champion itinerary.
-/

namespace BB6Coverage.Agent42RootResidueSix

open BB6ChampionArithmetic
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42MiddleSectionCountdown
open BB6Coverage.Agent41TM63ResidueSeven
open BB6Coverage.Agent44M2EvenSixGenericCounted
open BB6Coverage.Agent24M1ResidueFive

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add,h1]
  simp only [Option.bind_some]
  exact h2

/-- The genuine middle index is strictly below its binary width. -/
private theorem tm63_root_index_bound :
    tm63Index1 < 2^tm63Length1 :=
  tm63_index1_lt_pow_length1

theorem tm63_root_length_ge_four : 4 ≤ tm63Length1 := by
  have hA := tm63FirstSection_exponent_ge_five
  dsimp [tm63Length1]
  omega

def tm63RootResidueSixK : Nat := tm63RootMiddleK / 2

def tm63RootResidueSixA : Nat :=
  tm63MiddleAfter8A + tm63MiddleAfter8B + 1

def tm63RootResidueSixB : Nat :=
  2^tm63MiddleAfter8B - 1

def tm63RootResidueSixHead : Int :=
  tm63MiddleAfter8Head + 5 + 3*tm63MiddleAfter8B

/-- Since the seven-step quotient is odd, the residue-six index is
exactly 16*r+6 and lies below the root's binary width. -/
private theorem tm63_root_index_as_16r15 :
    tm63Index1 = 16*tm63RootResidueSixK + 15 := by
  simpa [tm63RootResidueSixK] using tm63_index1_eq_16k15

private theorem tm63_root_residue6_bound :
    16*tm63RootResidueSixK+6 < 2^tm63Length1 := by
  have hroot := tm63_root_index_bound
  have hindex := tm63_root_index_as_16r15
  have hsmall : 16*tm63RootResidueSixK+6 < tm63Index1 := by
    rw [hindex]
    omega
  exact lt_trans hsmall hroot

private theorem tm63_root_residue5_bound :
    16*tm63RootResidueSixK+5 < 2^tm63Length1 := by
  have hroot := tm63_root_index_bound
  have hindex := tm63_root_index_as_16r15
  have hsmall : 16*tm63RootResidueSixK+5 < tm63Index1 := by
    rw [hindex]
    omega
  exact lt_trans hsmall hroot

private theorem tm63_root_residue6_a_pos :
    0 < tm63RootResidueSixA := by
  dsimp [tm63RootResidueSixA]
  omega

def tm63MiddleAfter10A : Nat :=
  tm63RootResidueSixA + tm63RootResidueSixB + 2

def tm63MiddleAfter10B : Nat :=
  2^tm63RootResidueSixB - 1

def tm63MiddleAfter10Head : Int :=
  tm63RootResidueSixHead + 5 + 3*tm63RootResidueSixB

/-- Exact cumulative source-run length through the m=2,n=16*r+6 row. -/
def tm63MiddleFirst10Moves : Nat :=
  tm63MiddleFirst9Moves +
    proposedIncrementCost 2 (16*tm63RootResidueSixK+6)
      tm63RootResidueSixA tm63RootResidueSixB

/-- Append the quantified m=2,n=16*r+6 source increment and counted drain
to the authentic blank-root endpoint after the first nine rows. -/
theorem tm63_blank_reaches_after_middle10 :
    run tm2 tm63MiddleFirst10Moves blank =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK+5) 1
        tm63MiddleAfter10A 0 tm63MiddleAfter10B tm63MiddleAfter10Head) := by
  have hmul : 8*(2*tm63RootResidueSixK) = 16*tm63RootResidueSixK := by omega
  have hboundGeneric :
      8*(2*tm63RootResidueSixK)+6 < 2^tm63Length1 := by
    simpa [hmul] using tm63_root_residue6_bound
  have hrowGeneric := m2EvenSix_generic_counted_increment_source
    tm63Length1 (2*tm63RootResidueSixK)
    tm63RootResidueSixA tm63RootResidueSixB tm63RootResidueSixHead
    (by omega) hboundGeneric tm63_root_residue6_a_pos
  have hrow :
      run tm2 (proposedIncrementCost 2 (16*tm63RootResidueSixK+6)
        tm63RootResidueSixA tm63RootResidueSixB)
        (s1Config tm63Length1 (16*tm63RootResidueSixK+6) 2
          tm63RootResidueSixA 0 tm63RootResidueSixB tm63RootResidueSixHead) =
      some (s1Config tm63Length1 (16*tm63RootResidueSixK+5) 1
        (tm63RootResidueSixA+tm63RootResidueSixB+2) 0
        (2^tm63RootResidueSixB-1)
        (tm63RootResidueSixHead+5+3*tm63RootResidueSixB)) := by
    simpa [hmul] using hrowGeneric
  have hcomp := run_compose_local
    tm63_blank_reaches_after_middle9 hrow
  simpa [tm63MiddleFirst10Moves, tm63RootResidueSixK,
    tm63RootResidueSixA, tm63RootResidueSixB, tm63RootResidueSixHead,
    tm63MiddleAfter10A, tm63MiddleAfter10B, tm63MiddleAfter10Head] using hcomp

def tm63MiddleAfter11A : Nat :=
  nextExponent 1 tm63MiddleAfter10A tm63MiddleAfter10B

def tm63MiddleAfter11B : Nat :=
  nextRight tm63MiddleAfter10B

def tm63MiddleAfter11Head : Int :=
  tm63MiddleAfter10Head + 5 + 3*tm63MiddleAfter10B

/-- Exact cumulative source-run length through the following m=1,n=16*r+5
residue-five row. -/
def tm63MiddleFirst11Moves : Nat :=
  tm63MiddleFirst10Moves +
    proposedIncrementCost 1 (16*tm63RootResidueSixK+5)
      tm63MiddleAfter10A tm63MiddleAfter10B

private theorem tm63_after_middle10_a_pos :
    0 < tm63MiddleAfter10A := by
  dsimp [tm63MiddleAfter10A,tm63RootResidueSixA]
  omega

private theorem tm63_root_residue5_m1_bound :
    8*(2*tm63RootResidueSixK)+5 < 2^tm63Length1 := by
  have h := tm63_root_residue5_bound
  omega

/-- Append the existing m=1,n=8*q+5 residue-five source increment, with
q=2*r, to obtain one authentic blank-root run through eleven middle rows. -/
theorem tm63_blank_reaches_after_middle11 :
    run tm2 tm63MiddleFirst11Moves blank =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK+4) 0
        tm63MiddleAfter11A 0 tm63MiddleAfter11B tm63MiddleAfter11Head) := by
  have hL : 3 ≤ tm63Length1 := by
    have h := tm63_root_length_ge_four
    omega
  have hrow := m1ResidueFive_counted_increment_source_symbolic
    tm63Length1 (2*tm63RootResidueSixK)
    tm63MiddleAfter10A tm63MiddleAfter10B tm63MiddleAfter10Head
    hL tm63_root_residue5_m1_bound tm63_after_middle10_a_pos
  have hmul :
      8*(2*tm63RootResidueSixK) = 16*tm63RootResidueSixK := by omega
  have hrow' :
      run tm2
        (proposedIncrementCost 1 (16*tm63RootResidueSixK+5)
          tm63MiddleAfter10A tm63MiddleAfter10B)
        (s1Config tm63Length1 (16*tm63RootResidueSixK+5) 1
          tm63MiddleAfter10A 0 tm63MiddleAfter10B tm63MiddleAfter10Head) =
      some (s1Config tm63Length1 (16*tm63RootResidueSixK+4) 0
        tm63MiddleAfter11A 0 tm63MiddleAfter11B tm63MiddleAfter11Head) := by
    simpa [tm63MiddleAfter11A,tm63MiddleAfter11B,
      tm63MiddleAfter11Head,hmul] using hrow
  have hcomp := run_compose_local
    tm63_blank_reaches_after_middle10 hrow'
  simpa [tm63MiddleFirst11Moves] using hcomp

#print axioms tm63_root_length_ge_four
#print axioms tm63_blank_reaches_after_middle10
#print axioms tm63_blank_reaches_after_middle11

end BB6Coverage.Agent42RootResidueSix
