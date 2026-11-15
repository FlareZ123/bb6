import TM63MiddleSectionCountdown
import M0OddResidueSevenCounted
import Lean.Elab.Tactic.Omega

/-!
# Blank-root TM63 prefix through the (0,16*r+7) successor

Compose the genuine first-eight middle-section source itinerary with the
quantified original-table m=0, n=16*r+7 counted increment.  The resulting
blank-root run reaches the next m=2, n=16*r+6 row, exactly the family being
handled by the next root-row investigation.

This is a finite source-run composition, not a halting proof or a BB(6)
upper bound.
-/

namespace BB6Coverage.Agent41TM63ResidueSeven

open BB6Coverage
open BB6ChampionArithmetic
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42MiddleSectionPrefix4
open BB6Coverage.Agent42MiddleSectionCountdown
open BB6Coverage.Agent41M0OddResidueSevenCounted

private theorem nextExponent_pos_local (m a b : Nat) (ha : 0 < a) :
    0 < nextExponent m a b := by
  unfold nextExponent
  omega

private theorem run_compose_local
    {c d e : Config} {t u : Nat}
    (h1 : run tm2 t c = some d)
    (h2 : run tm2 u d = some e) :
    run tm2 (t+u) c = some e := by
  rw [run_add,h1]
  simpa using h2

private theorem tm63_middle_length_ge_four : 4 ≤ tm63Length1 := by
  have hA := tm63FirstSection_exponent_ge_five
  dsimp [tm63Length1]
  omega

private theorem tm63_middle_root_bound :
    8*tm63RootMiddleK+7 < 2^tm63Length1 := by
  have hA := tm63FirstSection_exponent_ge_five
  have hL : tm63Length1 = tm63FirstSection.exponent+5 := by
    dsimp [tm63Length1]
    omega
  have hp : 2^tm63Length1 =
      32*2^tm63FirstSection.exponent := by
    rw [hL,Nat.pow_add]
    norm_num
  rw [← tm63_index1_eq_8k7,tm63_index1_exact,hp]
  omega

private theorem tm63_middle_after8_a_pos :
    0 < tm63MiddleAfter8A := by
  have hroot : 0 < tm63FirstSection.right :=
    sectionResult_right_pos 7 2 6 63 (by decide)
  have ha1 := nextExponent_pos_local 2 tm63FirstSection.right
    (nextRight tm63FirstSection.right) hroot
  have ha2 := nextExponent_pos_local 1
    (middleAfter1A tm63FirstSection.right (nextRight tm63FirstSection.right))
    (middleAfter1B (nextRight tm63FirstSection.right)) ha1
  have ha3 := nextExponent_pos_local 0
    (middleAfter2A tm63FirstSection.right (nextRight tm63FirstSection.right))
    (middleAfter2B (nextRight tm63FirstSection.right)) ha2
  have ha4 := nextExponent_pos_local 2
    (middleAfter3A tm63FirstSection.right (nextRight tm63FirstSection.right))
    (middleAfter3B (nextRight tm63FirstSection.right)) ha3
  have ha5 := nextExponent_pos_local 1
    (middleAfter4A tm63FirstSection.right (nextRight tm63FirstSection.right))
    (middleAfter4B (nextRight tm63FirstSection.right)) ha4
  have ha6 := nextExponent_pos_local 0
    (middleAfter5A tm63FirstSection.right (nextRight tm63FirstSection.right))
    (middleAfter5B (nextRight tm63FirstSection.right)) ha5
  have ha7 := nextExponent_pos_local 2
    (middleAfter6A tm63FirstSection.right (nextRight tm63FirstSection.right))
    (middleAfter6B (nextRight tm63FirstSection.right)) ha6
  have ha8 := nextExponent_pos_local 1
    (middleAfter7A tm63FirstSection.right (nextRight tm63FirstSection.right))
    (middleAfter7B (nextRight tm63FirstSection.right)) ha7
  simpa [tm63MiddleAfter8A,middleAfter8A] using ha8

private theorem tm63_root_middle_k_split :
    tm63RootMiddleK = 2*(tm63RootMiddleK/2)+1 := by
  have hodd := tm63_root_middle_k_odd
  have hdiv := Nat.mod_add_div tm63RootMiddleK 2
  rw [hodd] at hdiv
  omega

private theorem tm63_root_residue7_index :
    16*(tm63RootMiddleK/2)+7 = 8*tm63RootMiddleK-1 := by
  rw [tm63_root_middle_k_split]
  omega

/-- Exact cost of the first eight middle rows followed by the (0,16*r+7)
root-specific counted increment. -/
def tm63MiddleFirst9Moves : Nat :=
  tm63AfterFirstResetMoves + tm63MiddleFirst8Moves +
    proposedIncrementCost 0 (8*tm63RootMiddleK-1)
      tm63MiddleAfter8A tm63MiddleAfter8B

/-- The original blank-root TM2 run reaches the next m=2, n=16*r+6 row.
All three components are source-run theorems over the original transition
table; the residue-seven theorem includes its exact counted drain. -/
theorem tm63_blank_reaches_after_middle9 :
    run tm2 tm63MiddleFirst9Moves blank =
      some (s1Config tm63Length1
        (16*(tm63RootMiddleK/2)+6) 2
        (tm63MiddleAfter8A+tm63MiddleAfter8B+1) 0
        (2^tm63MiddleAfter8B-1)
        (tm63MiddleAfter8Head+5+3*tm63MiddleAfter8B)) := by
  have hkSplit := tm63_root_middle_k_split
  have hindex := tm63_root_residue7_index
  have hL := tm63_middle_length_ge_four
  have hboundRoot := tm63_middle_root_bound
  have hbound : 16*(tm63RootMiddleK/2)+7 < 2^tm63Length1 := by
    rw [hindex]
    omega
  have hrow := m0Odd_residue7_counted_increment_source
    tm63Length1 (tm63RootMiddleK/2)
    tm63MiddleAfter8A tm63MiddleAfter8B tm63MiddleAfter8Head
    hL hbound tm63_middle_after8_a_pos
  have hrow' :
      run tm2 (proposedIncrementCost 0 (8*tm63RootMiddleK-1)
          tm63MiddleAfter8A tm63MiddleAfter8B)
        (s1Config tm63Length1 (8*tm63RootMiddleK-1) 0
          tm63MiddleAfter8A 0 tm63MiddleAfter8B tm63MiddleAfter8Head) =
      some (s1Config tm63Length1
        (16*(tm63RootMiddleK/2)+6) 2
        (tm63MiddleAfter8A+tm63MiddleAfter8B+1) 0
        (2^tm63MiddleAfter8B-1)
        (tm63MiddleAfter8Head+5+3*tm63MiddleAfter8B)) := by
    simpa [hindex] using hrow
  have hcomp := run_compose_local tm63_blank_reaches_after_middle8 hrow'
  simpa [tm63MiddleFirst9Moves] using hcomp

#print axioms tm63_blank_reaches_after_middle9

end BB6Coverage.Agent41TM63ResidueSeven
