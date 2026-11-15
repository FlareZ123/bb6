import TM63RootResidueSixteen
import M0EvenFourteenGenericSource
import Lean.Elab.Tactic.Omega

/-!
# Candidate blank-root source prefix through middle row 18

Compose Agent 49's root-certified middle-17 endpoint with the generic
m=0,n=32*k+14 source increment.  The root quotient is
k=tm63RootResidueSixK/2 because tm63RootResidueSixK is odd.
-/

namespace BB6Coverage.Agent48TM63RootMiddle18

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent49TM63RootResidueSixteen
open BB6Coverage.Agent48M0EvenFourteenGenericSource

set_option maxHeartbeats 3000000

def tm63MiddleAfter18A : Nat :=
  tm63MiddleAfter17A+tm63MiddleAfter17B+1

def tm63MiddleAfter18B : Nat :=
  2^tm63MiddleAfter17B-1

def tm63MiddleAfter18Head : Int :=
  tm63MiddleAfter17Head+5+3*tm63MiddleAfter17B

def tm63MiddleFirst18Moves : Nat :=
  tm63MiddleFirst17Moves+
    proposedIncrementCost 0 (16*tm63RootResidueSixK-2)
      tm63MiddleAfter17A tm63MiddleAfter17B

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add,h1]
  simp only [Option.bind_some]
  exact h2

/-- Candidate authentic blank-root source prefix through middle row 18.
The new row is m=0,n=16*r-2=32*k+14, with k=r/2. -/
theorem tm63_blank_reaches_after_middle18 :
    run tm2 tm63MiddleFirst18Moves blank =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-3) 2
        tm63MiddleAfter18A 0 tm63MiddleAfter18B
        tm63MiddleAfter18Head) := by
  have hrOdd := tm63_root_residue16_r_odd
  have hsplit :
      tm63RootResidueSixK =
        2*(tm63RootResidueSixK/2)+1 := by
    omega
  have hinput :
      32*(tm63RootResidueSixK/2)+14 =
        16*tm63RootResidueSixK-2 := by
    rw [hsplit]
    omega
  have htarget :
      32*(tm63RootResidueSixK/2)+13 =
        16*tm63RootResidueSixK-3 := by
    rw [hsplit]
    omega
  have hroot := tm63_index1_lt_pow_length1
  rw [tm63_root_index_eq_16r15] at hroot
  have hbound :
      32*(tm63RootResidueSixK/2)+14 < 2^tm63Length1 := by
    rw [hinput]
    omega
  have ha : 0 < tm63MiddleAfter17A := by
    unfold tm63MiddleAfter17A
    omega
  have hrow := m0EvenFourteen_counted_increment_source
    tm63Length1 (tm63RootResidueSixK/2)
    tm63MiddleAfter17A tm63MiddleAfter17B tm63MiddleAfter17Head
    tm63_root_length_ge_five hbound ha
  have hrow' :
      run tm2
        (proposedIncrementCost 0
          (16*tm63RootResidueSixK-2)
          tm63MiddleAfter17A tm63MiddleAfter17B)
        (s1Config tm63Length1
          (16*tm63RootResidueSixK-2) 0
          tm63MiddleAfter17A 0 tm63MiddleAfter17B
          tm63MiddleAfter17Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-3) 2
        (tm63MiddleAfter17A+tm63MiddleAfter17B+1) 0
        (2^tm63MiddleAfter17B-1)
        (tm63MiddleAfter17Head+5+3*tm63MiddleAfter17B)) := by
    simpa [hinput,htarget,tm63MiddleAfter18A,
      tm63MiddleAfter18B,tm63MiddleAfter18Head] using hrow
  have hcomp := run_compose_local
    tm63_blank_reaches_after_middle17 hrow'
  simpa [tm63MiddleFirst18Moves,tm63MiddleAfter18A,
    tm63MiddleAfter18B,tm63MiddleAfter18Head] using hcomp

#print axioms tm63_blank_reaches_after_middle18

end BB6Coverage.Agent48TM63RootMiddle18
