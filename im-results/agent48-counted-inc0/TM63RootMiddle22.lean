import TM63RootMiddle21
import M2EvenResidueTwoCounted
import Lean.Elab.Tactic.Omega

/-!
# Candidate authentic blank-root source prefix through middle row 22

Middle 21 ends at m=2,n=16*r-6.  This is exactly n=8*q+2 with
q=2*r-1, so compose Agent 42's generic m=2 residue-two counted increment.
The imported row and this root wrapper remain uncompiled candidates.
-/

namespace BB6Coverage.Agent48TM63RootMiddle22

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent49TM63RootResidueSixteen
open BB6Coverage.Agent48TM63RootMiddle21
open BB6Coverage.Agent48TM63RootMiddle20
open BB6Coverage.Agent42M2EvenResidueTwoCounted

set_option maxHeartbeats 3000000

def tm63MiddleAfter22A : Nat :=
  tm63MiddleAfter21A+tm63MiddleAfter21B+2

def tm63MiddleAfter22B : Nat :=
  2^tm63MiddleAfter21B-1

def tm63MiddleAfter22Head : Int :=
  tm63MiddleAfter21Head+5+3*tm63MiddleAfter21B

def tm63MiddleFirst22Moves : Nat :=
  tm63MiddleFirst21Moves+
    proposedIncrementCost 2 (16*tm63RootResidueSixK-6)
      tm63MiddleAfter21A tm63MiddleAfter21B

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add,h1]
  simp only [Option.bind_some]
  exact h2

/-- Candidate authentic blank-root source prefix through middle row 22.
The new row is m=2,n=16*r-6=8*(2*r-1)+2, reaching m=1,n=16*r-7. -/
theorem tm63_blank_reaches_after_middle22 :
    run tm2 tm63MiddleFirst22Moves blank =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-7) 1
        tm63MiddleAfter22A 0 tm63MiddleAfter22B
        tm63MiddleAfter22Head) := by
  have hrOdd := tm63_root_residue16_r_odd
  have hrPos : 0 < tm63RootResidueSixK := by omega
  have hinput :
      8*tm63Middle20ResidueK+2 =
        16*tm63RootResidueSixK-6 := by
    simp [tm63Middle20ResidueK]
    omega
  have htarget :
      8*tm63Middle20ResidueK+1 =
        16*tm63RootResidueSixK-7 := by
    simp [tm63Middle20ResidueK]
    omega
  have hindex :
      tm63Index1 = 16*tm63RootResidueSixK+15 := by
    simpa [tm63RootResidueSixK] using tm63_index1_eq_16k15
  have hroot := tm63_index1_lt_pow_length1
  rw [hindex] at hroot
  have hL : 3 ≤ tm63Length1 := by
    have hL4 := tm63_root_length_ge_four
    omega
  have hbound :
      8*tm63Middle20ResidueK+2 < 2^tm63Length1 := by
    rw [hinput]
    omega
  have ha : 0 < tm63MiddleAfter21A := by
    unfold tm63MiddleAfter21A
    omega
  have hrow := m2Even_residue2_counted_increment_source
    tm63Length1 tm63Middle20ResidueK
    tm63MiddleAfter21A tm63MiddleAfter21B tm63MiddleAfter21Head
    hL hbound ha
  have hrow' :
      run tm2
        (proposedIncrementCost 2
          (16*tm63RootResidueSixK-6)
          tm63MiddleAfter21A tm63MiddleAfter21B)
        (s1Config tm63Length1
          (16*tm63RootResidueSixK-6) 2
          tm63MiddleAfter21A 0 tm63MiddleAfter21B
          tm63MiddleAfter21Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-7) 1
        (tm63MiddleAfter21A+tm63MiddleAfter21B+2) 0
        (2^tm63MiddleAfter21B-1)
        (tm63MiddleAfter21Head+5+3*tm63MiddleAfter21B)) := by
    simpa [hinput,htarget,tm63MiddleAfter22A,
      tm63MiddleAfter22B,tm63MiddleAfter22Head] using hrow
  have hcomp := run_compose_local
    tm63_blank_reaches_after_middle21 hrow'
  simpa [tm63MiddleFirst22Moves,tm63MiddleAfter22A,
    tm63MiddleAfter22B,tm63MiddleAfter22Head] using hcomp

#print axioms tm63_blank_reaches_after_middle22

end BB6Coverage.Agent48TM63RootMiddle22
