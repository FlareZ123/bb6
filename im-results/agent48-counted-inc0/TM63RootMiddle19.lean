import TM63RootMiddle18
import M2OddGenericStage
import Lean.Elab.Tactic.Omega

/-!
# Candidate blank-root source prefix through middle row 19

Middle 18 ends at m=2,n=16*r-3, which is odd.  Compose the already
generic m=2 odd counted increment to reach m=1,n=16*r-4.
-/

namespace BB6Coverage.Agent48TM63RootMiddle19

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent49TM63RootResidueSixteen
open BB6Coverage.Agent48TM63RootMiddle18
open BB6Coverage.Agent42M2OddGeneric

set_option maxHeartbeats 3000000

def tm63MiddleAfter19A : Nat :=
  tm63MiddleAfter18A+tm63MiddleAfter18B+2

def tm63MiddleAfter19B : Nat :=
  2^tm63MiddleAfter18B-1

def tm63MiddleAfter19Head : Int :=
  tm63MiddleAfter18Head+5+3*tm63MiddleAfter18B

def tm63MiddleFirst19Moves : Nat :=
  tm63MiddleFirst18Moves+
    proposedIncrementCost 2 (16*tm63RootResidueSixK-3)
      tm63MiddleAfter18A tm63MiddleAfter18B

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add,h1]
  simp only [Option.bind_some]
  exact h2

/-- Candidate authentic blank-root source prefix through middle row 19. -/
theorem tm63_blank_reaches_after_middle19 :
    run tm2 tm63MiddleFirst19Moves blank =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-4) 1
        tm63MiddleAfter19A 0 tm63MiddleAfter19B
        tm63MiddleAfter19Head) := by
  have hrOdd := tm63_root_residue16_r_odd
  have hindex :
      tm63Index1 = 16*tm63RootResidueSixK+15 := by
    simpa [tm63RootResidueSixK] using tm63_index1_eq_16k15
  have hroot := tm63_index1_lt_pow_length1
  rw [hindex] at hroot
  have hbound : 16*tm63RootResidueSixK-3 < 2^tm63Length1 := by
    omega
  have hn : (16*tm63RootResidueSixK-3) % 2 = 1 := by
    omega
  have hrow := m2Odd_counted_increment_source
    tm63Length1 (16*tm63RootResidueSixK-3)
    tm63MiddleAfter18A tm63MiddleAfter18B tm63MiddleAfter18Head
    hn hbound
  have hrow' :
      run tm2
        (proposedIncrementCost 2
          (16*tm63RootResidueSixK-3)
          tm63MiddleAfter18A tm63MiddleAfter18B)
        (s1Config tm63Length1
          (16*tm63RootResidueSixK-3) 2
          tm63MiddleAfter18A 0 tm63MiddleAfter18B
          tm63MiddleAfter18Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-4) 1
        (tm63MiddleAfter18A+tm63MiddleAfter18B+2) 0
        (2^tm63MiddleAfter18B-1)
        (tm63MiddleAfter18Head+5+3*tm63MiddleAfter18B)) := by
    simpa [tm63MiddleAfter19A,tm63MiddleAfter19B,
      tm63MiddleAfter19Head] using hrow
  have hcomp := run_compose_local
    tm63_blank_reaches_after_middle18 hrow'
  simpa [tm63MiddleFirst19Moves,tm63MiddleAfter19A,
    tm63MiddleAfter19B,tm63MiddleAfter19Head] using hcomp

#print axioms tm63_blank_reaches_after_middle19

end BB6Coverage.Agent48TM63RootMiddle19
