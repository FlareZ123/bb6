import TM63RootMiddle22
import M1OddResidueOneSource
import Lean.Elab.Tactic.Omega

/-!
# Candidate authentic blank-root source prefix through middle row 23

Middle 22 ends at m=1,n=16*r-7.  Since
16*r-7 = 8*(2*r-1)+1, apply the general m=1 residue-one counted
increment.  This is a source-level composition candidate; its imports
must pass the dedicated original-source audit before it is treated as
an established root-prefix theorem.
-/

namespace BB6Coverage.Agent48TM63RootMiddle23

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent49TM63RootResidueSixteen
open BB6Coverage.Agent48TM63RootMiddle22
open BB6Coverage.Agent48M1OddResidueOneSource

set_option maxHeartbeats 3000000

def tm63MiddleAfter23A : Nat :=
  tm63MiddleAfter22A+tm63MiddleAfter22B+2

def tm63MiddleAfter23B : Nat :=
  2^tm63MiddleAfter22B-1

def tm63MiddleAfter23Head : Int :=
  tm63MiddleAfter22Head+5+3*tm63MiddleAfter22B

def tm63MiddleFirst23Moves : Nat :=
  tm63MiddleFirst22Moves+
    proposedIncrementCost 1 (16*tm63RootResidueSixK-7)
      tm63MiddleAfter22A tm63MiddleAfter22B

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add,h1]
  simp only [Option.bind_some]
  exact h2

/-- Candidate authentic blank-root source prefix through middle row 23.
The new row is m=1,n=16*r-7=8*(2*r-1)+1, reaching m=0,n=16*r-8. -/
theorem tm63_blank_reaches_after_middle23 :
    run tm2 tm63MiddleFirst23Moves blank =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-8) 0
        tm63MiddleAfter23A 0 tm63MiddleAfter23B
        tm63MiddleAfter23Head) := by
  have hrOdd := tm63_root_residue16_r_odd
  have hrPos : 0 < tm63RootResidueSixK := by omega
  have hinput :
      8*(2*tm63RootResidueSixK-1)+1 =
        16*tm63RootResidueSixK-7 := by omega
  have htarget :
      8*(2*tm63RootResidueSixK-1) =
        16*tm63RootResidueSixK-8 := by omega
  have hindex :
      tm63Index1 = 16*tm63RootResidueSixK+15 := by
    simpa [tm63RootResidueSixK] using tm63_index1_eq_16k15
  have hroot := tm63_index1_lt_pow_length1
  rw [hindex] at hroot
  have hL : 3 ≤ tm63Length1 := by
    have hL4 := tm63_root_length_ge_four
    omega
  have hbound :
      8*(2*tm63RootResidueSixK-1)+1 < 2^tm63Length1 := by
    rw [hinput]
    omega
  have ha : 0 < tm63MiddleAfter22A := by
    unfold tm63MiddleAfter22A
    omega
  have hrow := m1OddResidueOne_counted_increment_source
    tm63Length1 (2*tm63RootResidueSixK-1)
    tm63MiddleAfter22A tm63MiddleAfter22B tm63MiddleAfter22Head
    hL hbound ha
  have hrow' :
      run tm2
        (proposedIncrementCost 1
          (16*tm63RootResidueSixK-7)
          tm63MiddleAfter22A tm63MiddleAfter22B)
        (s1Config tm63Length1
          (16*tm63RootResidueSixK-7) 1
          tm63MiddleAfter22A 0 tm63MiddleAfter22B
          tm63MiddleAfter22Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-8) 0
        (tm63MiddleAfter22A+tm63MiddleAfter22B+2) 0
        (2^tm63MiddleAfter22B-1)
        (tm63MiddleAfter22Head+5+3*tm63MiddleAfter22B)) := by
    simpa [hinput,htarget,tm63MiddleAfter23A,
      tm63MiddleAfter23B,tm63MiddleAfter23Head] using hrow
  have hcomp := run_compose_local
    tm63_blank_reaches_after_middle22 hrow'
  simpa [tm63MiddleFirst23Moves,tm63MiddleAfter23A,
    tm63MiddleAfter23B,tm63MiddleAfter23Head] using hcomp

#print axioms tm63_blank_reaches_after_middle23

end BB6Coverage.Agent48TM63RootMiddle23
