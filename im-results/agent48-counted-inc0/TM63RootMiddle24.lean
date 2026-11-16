import TM63RootMiddle23
import M0EvenEightGenericSource
import Lean.Elab.Tactic.Omega

/-!
# Candidate authentic blank-root source prefix through middle row 24

Middle 23 ends at m=0,n=16*r-8=8*(2*r-1), with odd quotient q=2*r-1.
The generic M0-even 8q source increment reaches m=2,n=16*r-9.
This file is a root composition candidate until the imported source closures
pass the original-source Lean and transitive-axiom gates.
-/

namespace BB6Coverage.Agent48TM63RootMiddle24

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent49TM63RootResidueSixteen
open BB6Coverage.Agent48TM63RootMiddle23
open BB6Coverage.Agent48M0EvenEightGenericSource
open BB6Coverage.Agent48CountedInc0

set_option maxHeartbeats 3000000

def tm63MiddleAfter24A : Nat :=
  tm63MiddleAfter23A+tm63MiddleAfter23B+1

def tm63MiddleAfter24B : Nat :=
  2^tm63MiddleAfter23B-1

def tm63MiddleAfter24Head : Int :=
  tm63MiddleAfter23Head+5+3*tm63MiddleAfter23B

def tm63MiddleFirst24Moves : Nat :=
  tm63MiddleFirst23Moves+
    proposedIncrementCost 0 (16*tm63RootResidueSixK-8)
      tm63MiddleAfter23A tm63MiddleAfter23B

/-- Exact closed cost of the newly added middle-24 row. -/
theorem tm63_middle24_row_cost :
    proposedIncrementCost 0 (16*tm63RootResidueSixK-8)
      tm63MiddleAfter23A tm63MiddleAfter23B =
    6*4^tm63MiddleAfter23B + 42*2^tm63MiddleAfter23B +
      12*tm63MiddleAfter23A - 9*tm63MiddleAfter23B + 51 := by
  have hqOdd : (2*tm63RootResidueSixK-1)%2 = 1 := by omega
  have h := m0EvenEight_proposedIncrementCost_closed
    (2*tm63RootResidueSixK-1)
    tm63MiddleAfter23A tm63MiddleAfter23B hqOdd
  simpa [show 8*(2*tm63RootResidueSixK-1) =
    16*tm63RootResidueSixK-8 by omega] using h

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add,h1]
  simp only [Option.bind_some]
  exact h2

/-- Candidate authentic blank-root source prefix through middle row 24.
The new row is m=0,n=16*r-8=8*(2*r-1), reaching m=2,n=16*r-9. -/
theorem tm63_blank_reaches_after_middle24 :
    run tm2 tm63MiddleFirst24Moves blank =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-9) 2
        tm63MiddleAfter24A 0 tm63MiddleAfter24B
        tm63MiddleAfter24Head) := by
  have hrOdd := tm63_root_residue16_r_odd
  have hrPos : 0 < tm63RootResidueSixK := by omega
  have hqOdd : (2*tm63RootResidueSixK-1)%2 = 1 := by omega
  have hinput :
      8*(2*tm63RootResidueSixK-1) =
        16*tm63RootResidueSixK-8 := by omega
  have htarget :
      8*(2*tm63RootResidueSixK-1)-1 =
        16*tm63RootResidueSixK-9 := by omega
  have hindex :
      tm63Index1 = 16*tm63RootResidueSixK+15 := by
    simpa [tm63RootResidueSixK] using tm63_index1_eq_16k15
  have hroot := tm63_index1_lt_pow_length1
  rw [hindex] at hroot
  have hL : 4 ≤ tm63Length1 := tm63_root_length_ge_four
  have hbound :
      8*(2*tm63RootResidueSixK-1) < 2^tm63Length1 := by
    rw [hinput]
    omega
  have ha : 0 < tm63MiddleAfter23A := by
    unfold tm63MiddleAfter23A
    omega
  have hrow := m0EvenEight_counted_increment_source
    tm63Length1 (2*tm63RootResidueSixK-1)
    tm63MiddleAfter23A tm63MiddleAfter23B tm63MiddleAfter23Head
    hL hqOdd hbound ha
  have hrow' :
      run tm2
        (proposedIncrementCost 0
          (16*tm63RootResidueSixK-8)
          tm63MiddleAfter23A tm63MiddleAfter23B)
        (s1Config tm63Length1
          (16*tm63RootResidueSixK-8) 0
          tm63MiddleAfter23A 0 tm63MiddleAfter23B
          tm63MiddleAfter23Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-9) 2
        (tm63MiddleAfter23A+tm63MiddleAfter23B+1) 0
        (2^tm63MiddleAfter23B-1)
        (tm63MiddleAfter23Head+5+(3*tm63MiddleAfter23B:Int))) := by
    simpa [hinput,htarget,tm63MiddleAfter24A,
      tm63MiddleAfter24B,tm63MiddleAfter24Head] using hrow
  have hcomp := run_compose_local
    tm63_blank_reaches_after_middle23 hrow'
  simpa [tm63MiddleFirst24Moves,tm63MiddleAfter24A,
    tm63MiddleAfter24B,tm63MiddleAfter24Head] using hcomp

#print axioms tm63_middle24_row_cost
#print axioms tm63_blank_reaches_after_middle24

end BB6Coverage.Agent48TM63RootMiddle24
