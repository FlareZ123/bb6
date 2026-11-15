import TM63RootMiddle19
import M1EvenResidueFourSource
import Lean.Elab.Tactic.Omega

/-!
# Candidate authentic blank-root source prefix through middle row 20

Middle 19 ends at m=1,n=16*r-4.  This is exactly n=8*q+4 with
q=2*r-1, so compose Agent 41's generic m=1 residue-four counted increment.
This wrapper is source-only until its imported source closure is Lean-checked.
-/

namespace BB6Coverage.Agent48TM63RootMiddle20

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent49TM63RootResidueSixteen
open BB6Coverage.Agent48TM63RootMiddle19
open BB6Coverage.Agent41M1EvenResidueFour

set_option maxHeartbeats 3000000

/-- The residue quotient identifying 16*r-4 with 8*q+4. -/
def tm63Middle20ResidueK : Nat :=
  2*tm63RootResidueSixK-1

def tm63MiddleAfter20A : Nat :=
  tm63MiddleAfter19A+tm63MiddleAfter19B+2

def tm63MiddleAfter20B : Nat :=
  2^tm63MiddleAfter19B-1

def tm63MiddleAfter20Head : Int :=
  tm63MiddleAfter19Head+5+3*tm63MiddleAfter19B

def tm63MiddleFirst20Moves : Nat :=
  tm63MiddleFirst19Moves+
    proposedIncrementCost 1 (16*tm63RootResidueSixK-4)
      tm63MiddleAfter19A tm63MiddleAfter19B

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add,h1]
  simp only [Option.bind_some]
  exact h2

/-- Candidate authentic blank-root source prefix through middle row 20.
The new row is m=1,n=16*r-4=8*(2*r-1)+4, reaching m=0,n=16*r-5. -/
theorem tm63_blank_reaches_after_middle20 :
    run tm2 tm63MiddleFirst20Moves blank =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-5) 0
        tm63MiddleAfter20A 0 tm63MiddleAfter20B
        tm63MiddleAfter20Head) := by
  have hrOdd := tm63_root_residue16_r_odd
  have hrPos : 0 < tm63RootResidueSixK := by omega
  have hinput :
      8*tm63Middle20ResidueK+4 =
        16*tm63RootResidueSixK-4 := by
    simp [tm63Middle20ResidueK]
    omega
  have htarget :
      8*tm63Middle20ResidueK+3 =
        16*tm63RootResidueSixK-5 := by
    simp [tm63Middle20ResidueK]
    omega
  have hindex :
      tm63Index1 = 16*tm63RootResidueSixK+15 := by
    simpa [tm63RootResidueSixK] using tm63_index1_eq_16k15
  have hroot := tm63_index1_lt_pow_length1
  rw [hindex] at hroot
  have hL : 3 ≤ tm63Length1 := by
    dsimp [tm63Length1]
    omega
  have hbound :
      8*tm63Middle20ResidueK+4 < 2^tm63Length1 := by
    rw [hinput]
    omega
  have ha : 0 < tm63MiddleAfter19A := by
    unfold tm63MiddleAfter19A
    omega
  have hrow := m1EvenResidueFour_counted_increment_source
    tm63Length1 tm63Middle20ResidueK
    tm63MiddleAfter19A tm63MiddleAfter19B tm63MiddleAfter19Head
    hL hbound ha
  have hrow' :
      run tm2
        (proposedIncrementCost 1
          (16*tm63RootResidueSixK-4)
          tm63MiddleAfter19A tm63MiddleAfter19B)
        (s1Config tm63Length1
          (16*tm63RootResidueSixK-4) 1
          tm63MiddleAfter19A 0 tm63MiddleAfter19B
          tm63MiddleAfter19Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-5) 0
        (tm63MiddleAfter19A+tm63MiddleAfter19B+2) 0
        (2^tm63MiddleAfter19B-1)
        (tm63MiddleAfter19Head+5+3*tm63MiddleAfter19B)) := by
    simpa [hinput,htarget,tm63MiddleAfter20A,
      tm63MiddleAfter20B,tm63MiddleAfter20Head] using hrow
  have hcomp := run_compose_local
    tm63_blank_reaches_after_middle19 hrow'
  simpa [tm63MiddleFirst20Moves,tm63MiddleAfter20A,
    tm63MiddleAfter20B,tm63MiddleAfter20Head] using hcomp

#print axioms tm63_blank_reaches_after_middle20

end BB6Coverage.Agent48TM63RootMiddle20
