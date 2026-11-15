import TM63RootMiddle20
import M0OddGenericSource
import Lean.Elab.Tactic.Omega

/-!
# Candidate authentic blank-root source prefix through middle row 21

The m=1 residue-four row reaches m=0,n=16*r-5, which is odd.
Reuse the existing generic all-odd m=0 counted increment to reach
m=2,n=16*r-6.  This is the predecessor state needed by the distinct
m=2 residue-two row owned by Agent 42.
-/

namespace BB6Coverage.Agent48TM63RootMiddle21

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent49TM63RootResidueSixteen
open BB6Coverage.Agent48TM63RootMiddle20
open BB6Coverage.Agent48M0OddGenericSource

set_option maxHeartbeats 3000000

def tm63MiddleAfter21A : Nat :=
  tm63MiddleAfter20A+tm63MiddleAfter20B+1

def tm63MiddleAfter21B : Nat :=
  2^tm63MiddleAfter20B-1

def tm63MiddleAfter21Head : Int :=
  tm63MiddleAfter20Head+5+3*tm63MiddleAfter20B

def tm63MiddleFirst21Moves : Nat :=
  tm63MiddleFirst20Moves+
    proposedIncrementCost 0 (16*tm63RootResidueSixK-5)
      tm63MiddleAfter20A tm63MiddleAfter20B

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add,h1]
  simp only [Option.bind_some]
  exact h2

/-- Candidate authentic blank-root source prefix through middle row 21.
The new row is the generic m=0 odd increment at n=16*r-5. -/
theorem tm63_blank_reaches_after_middle21 :
    run tm2 tm63MiddleFirst21Moves blank =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-6) 2
        tm63MiddleAfter21A 0 tm63MiddleAfter21B
        tm63MiddleAfter21Head) := by
  have hrOdd := tm63_root_residue16_r_odd
  have hrPos : 0 < tm63RootResidueSixK := by omega
  have hindex :
      tm63Index1 = 16*tm63RootResidueSixK+15 := by
    simpa [tm63RootResidueSixK] using tm63_index1_eq_16k15
  have hroot := tm63_index1_lt_pow_length1
  rw [hindex] at hroot
  have hL : 0 < tm63Length1 := by
    dsimp [tm63Length1]
    omega
  have hn : (16*tm63RootResidueSixK-5)%2=1 := by omega
  have hbound :
      16*tm63RootResidueSixK-5 < 2^tm63Length1 := by omega
  have ha : 0 < tm63MiddleAfter20A := by
    unfold tm63MiddleAfter20A
    omega
  have hrow := m0Odd_counted_increment_source
    tm63Length1 (16*tm63RootResidueSixK-5)
    tm63MiddleAfter20A tm63MiddleAfter20B tm63MiddleAfter20Head
    hL hn hbound ha
  have hrow' :
      run tm2
        (proposedIncrementCost 0
          (16*tm63RootResidueSixK-5)
          tm63MiddleAfter20A tm63MiddleAfter20B)
        (s1Config tm63Length1
          (16*tm63RootResidueSixK-5) 0
          tm63MiddleAfter20A 0 tm63MiddleAfter20B
          tm63MiddleAfter20Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-6) 2
        (tm63MiddleAfter20A+tm63MiddleAfter20B+1) 0
        (2^tm63MiddleAfter20B-1)
        (tm63MiddleAfter20Head+5+3*tm63MiddleAfter20B)) := by
    simpa [tm63MiddleAfter21A,tm63MiddleAfter21B,
      tm63MiddleAfter21Head] using hrow
  have hcomp := run_compose_local
    tm63_blank_reaches_after_middle20 hrow'
  simpa [tm63MiddleFirst21Moves,tm63MiddleAfter21A,
    tm63MiddleAfter21B,tm63MiddleAfter21Head] using hcomp

#print axioms tm63_blank_reaches_after_middle21

end BB6Coverage.Agent48TM63RootMiddle21
