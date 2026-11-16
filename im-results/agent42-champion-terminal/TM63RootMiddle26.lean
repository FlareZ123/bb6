import TM63RootMiddle25
import M1EvenResidueSix
import Lean.Elab.Tactic.Omega

/-!
# Candidate authentic blank-root source prefix through middle row 26

Middle 25 ends at marker 1 with n=16*r-10=8*(2*r-2)+6.
The all-parameter m=1 residue-six counted increment reaches marker 0,
n=16*r-11.  The quotient is nonnegative because the root parameter r
is odd.  This is a root composition candidate until the full imported
source chain passes the original-source and transitive-axiom audit.
-/

namespace BB6Coverage.Agent42TM63RootMiddle26

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent49TM63RootResidueSixteen
open BB6Coverage.Agent42TM63RootMiddle25
open BB6Coverage.Agent42M1EvenResidueSix
open BB6ChampionArithmetic

set_option maxHeartbeats 3000000

def tm63MiddleAfter26A : Nat :=
  tm63MiddleAfter25A+tm63MiddleAfter25B+2

def tm63MiddleAfter26B : Nat :=
  2^tm63MiddleAfter25B-1

def tm63MiddleAfter26Head : Int :=
  tm63MiddleAfter25Head+5+3*tm63MiddleAfter25B

def tm63MiddleFirst26Moves : Nat :=
  tm63MiddleFirst25Moves+
    proposedIncrementCost 1 (16*tm63RootResidueSixK-10)
      tm63MiddleAfter25A tm63MiddleAfter25B

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add,h1]
  simp only [Option.bind_some]
  exact h2

/-- Candidate authentic blank-root source prefix through middle row 26.
The m=1 residue-six row sends n=16*r-10 to n=16*r-11. -/
theorem tm63_blank_reaches_after_middle26 :
    run tm2 tm63MiddleFirst26Moves blank =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-11) 0
        tm63MiddleAfter26A 0 tm63MiddleAfter26B
        tm63MiddleAfter26Head) := by
  have hrOdd := tm63_root_residue16_r_odd
  have hrPos : 0 < tm63RootResidueSixK := by omega
  have hindex :
      tm63Index1 = 16*tm63RootResidueSixK+15 := by
    simpa [tm63RootResidueSixK] using tm63_index1_eq_16k15
  have hroot := tm63_index1_lt_pow_length1
  rw [hindex] at hroot
  have hL : 3 ≤ tm63Length1 := tm63_root_length_ge_four
  have hinput :
      8*(2*tm63RootResidueSixK-2)+6 =
        16*tm63RootResidueSixK-10 := by omega
  have htarget :
      8*(2*tm63RootResidueSixK-2)+5 =
        16*tm63RootResidueSixK-11 := by omega
  have hbound :
      8*(2*tm63RootResidueSixK-2)+6 < 2^tm63Length1 := by
    rw [hinput]
    omega
  have ha : 0 < tm63MiddleAfter25A := by
    unfold tm63MiddleAfter25A
    omega
  have hrow := m1Even_residue6_counted_increment_source
    tm63Length1 (2*tm63RootResidueSixK-2)
    tm63MiddleAfter25A tm63MiddleAfter25B
    tm63MiddleAfter25Head hL hbound ha
  have hrow' :
      run tm2
        (proposedIncrementCost 1
          (16*tm63RootResidueSixK-10)
          tm63MiddleAfter25A tm63MiddleAfter25B)
        (s1Config tm63Length1
          (16*tm63RootResidueSixK-10) 1
          tm63MiddleAfter25A 0 tm63MiddleAfter25B
          tm63MiddleAfter25Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-11) 0
        (tm63MiddleAfter25A+tm63MiddleAfter25B+2) 0
        (2^tm63MiddleAfter25B-1)
        (tm63MiddleAfter25Head+5+3*tm63MiddleAfter25B)) := by
    simpa [hinput,htarget,tm63MiddleAfter26A,
      tm63MiddleAfter26B,tm63MiddleAfter26Head] using hrow
  have hcomp := run_compose_local
    tm63_blank_reaches_after_middle25 hrow'
  simpa [tm63MiddleFirst26Moves,tm63MiddleAfter26A,
    tm63MiddleAfter26B,tm63MiddleAfter26Head] using hcomp

#print axioms tm63_blank_reaches_after_middle26

end BB6Coverage.Agent42TM63RootMiddle26
