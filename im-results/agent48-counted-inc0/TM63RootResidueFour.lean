import TM63RootResidueSix
import M0EvenResidueFour
import Lean.Elab.Tactic.Omega

/-!
# Append the M0-even n=16*r+4 row to the authentic TM63 root

This file is a root-composition candidate only. Its source increment
dependency is in M0EvenResidueFour.lean; that dependency and the
preceding middle-11 chain still require their original-import compile
and transitive axiom audits.
-/

namespace BB6Coverage.Agent48TM63RootResidueFour

open BB6Coverage
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent24ChampionArithmetic
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent48M0EvenResidueFour

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add,h1]
  simp only [Option.bind_some]
  exact h2

/-- The next n=16*r+4 source index is below the root's binary width. -/
private theorem tm63_root_residue4_bound :
    16*tm63RootResidueSixK+4 < 2^tm63Length1 := by
  have hroot := tm63_index1_lt_pow_length1
  have hindex :
      tm63Index1 = 16*tm63RootResidueSixK+15 := by
    simpa [tm63RootResidueSixK] using tm63_index1_eq_16k15
  have hsmall : 16*tm63RootResidueSixK+4 < tm63Index1 := by
    rw [hindex]
    omega
  exact lt_trans hsmall hroot

private theorem tm63_root_length_ge_three : 3 ≤ tm63Length1 := by
  have hA := tm63FirstSection_exponent_ge_five
  dsimp [tm63Length1]
  omega

private theorem tm63_after_middle11_a_pos :
    0 < tm63MiddleAfter11A := by
  unfold tm63MiddleAfter11A nextExponent
  omega

def tm63MiddleAfter12A : Nat :=
  tm63MiddleAfter11A + tm63MiddleAfter11B + 1

def tm63MiddleAfter12B : Nat :=
  2^tm63MiddleAfter11B - 1

def tm63MiddleAfter12Head : Int :=
  tm63MiddleAfter11Head + 5 + 3*tm63MiddleAfter11B

/-- Exact cumulative successful-transition count through the next Rst0 row. -/
def tm63MiddleFirst12Moves : Nat :=
  tm63MiddleFirst11Moves +
    proposedIncrementCost 0 (16*tm63RootResidueSixK+4)
      tm63MiddleAfter11A tm63MiddleAfter11B

/-- Extend the genuine blank-root trajectory through middle row 12:
m=0,n=16*r+4 → m=2,n=16*r+3. -/
theorem tm63_blank_reaches_after_middle12 :
    run tm2 tm63MiddleFirst12Moves blank =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK+3) 2
        tm63MiddleAfter12A 0 tm63MiddleAfter12B tm63MiddleAfter12Head) := by
  have hL := tm63_root_length_ge_three
  have hbound : 8*(2*tm63RootResidueSixK)+4 < 2^tm63Length1 := by
    have h := tm63_root_residue4_bound
    omega
  have ha := tm63_after_middle11_a_pos
  have hrow := m0Even_residue4_counted_increment_source
    tm63Length1 (2*tm63RootResidueSixK)
    tm63MiddleAfter11A tm63MiddleAfter11B tm63MiddleAfter11Head
    hL hbound ha
  have hmul : 8*(2*tm63RootResidueSixK)+4 =
      16*tm63RootResidueSixK+4 := by omega
  have hrow' :
      run tm2
        (proposedIncrementCost 0 (16*tm63RootResidueSixK+4)
          tm63MiddleAfter11A tm63MiddleAfter11B)
        (s1Config tm63Length1 (16*tm63RootResidueSixK+4) 0
          tm63MiddleAfter11A 0 tm63MiddleAfter11B tm63MiddleAfter11Head) =
      some (s1Config tm63Length1 (16*tm63RootResidueSixK+3) 2
        tm63MiddleAfter12A 0 tm63MiddleAfter12B tm63MiddleAfter12Head) := by
    simpa [hmul,tm63MiddleAfter12A,tm63MiddleAfter12B,
      tm63MiddleAfter12Head] using hrow
  have hcomp := run_compose_local
    tm63_blank_reaches_after_middle11 hrow'
  simpa [tm63MiddleFirst12Moves] using hcomp

#print axioms tm63_blank_reaches_after_middle12

end BB6Coverage.Agent48TM63RootResidueFour
