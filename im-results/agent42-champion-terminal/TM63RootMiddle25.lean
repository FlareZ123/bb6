import TM63RootMiddle24
import M2OddGenericStage
import Lean.Elab.Tactic.Omega

/-!
# Candidate authentic blank-root source prefix through middle row 25

Middle 24 ends at marker 2 with n=16*r-9, which is odd.  The generic
original-source m=2 odd counted increment takes it to marker 1,
n=16*r-10.  This composes an already-developed generic row with the
authentic-root endpoint; the complete imported chain still needs its
original-source Lean and transitive-axiom audit.
-/

namespace BB6Coverage.Agent42TM63RootMiddle25

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent49TM63RootResidueSixteen
open BB6Coverage.Agent48TM63RootMiddle24
open BB6Coverage.Agent42M2OddGeneric
open BB6ChampionArithmetic

set_option maxHeartbeats 3000000

def tm63MiddleAfter25A : Nat :=
  tm63MiddleAfter24A+tm63MiddleAfter24B+2

def tm63MiddleAfter25B : Nat :=
  2^tm63MiddleAfter24B-1

def tm63MiddleAfter25Head : Int :=
  tm63MiddleAfter24Head+5+3*tm63MiddleAfter24B

def tm63MiddleFirst25Moves : Nat :=
  tm63MiddleFirst24Moves+
    proposedIncrementCost 2 (16*tm63RootResidueSixK-9)
      tm63MiddleAfter24A tm63MiddleAfter24B

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add,h1]
  simp only [Option.bind_some]
  exact h2

/-- Candidate authentic blank-root source prefix through middle row 25.
The m=2 odd row sends n=16*r-9 to n=16*r-10. -/
theorem tm63_blank_reaches_after_middle25 :
    run tm2 tm63MiddleFirst25Moves blank =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-10) 1
        tm63MiddleAfter25A 0 tm63MiddleAfter25B
        tm63MiddleAfter25Head) := by
  have hrOdd := tm63_root_residue16_r_odd
  have hrPos : 0 < tm63RootResidueSixK := by omega
  have hindex :
      tm63Index1 = 16*tm63RootResidueSixK+15 := by
    simpa [tm63RootResidueSixK] using tm63_index1_eq_16k15
  have hroot := tm63_index1_lt_pow_length1
  rw [hindex] at hroot
  have hn : (16*tm63RootResidueSixK-9)%2 = 1 := by omega
  have hbound :
      16*tm63RootResidueSixK-9 < 2^tm63Length1 := by omega
  have hrow := m2Odd_counted_increment_source
    tm63Length1 (16*tm63RootResidueSixK-9)
    tm63MiddleAfter24A tm63MiddleAfter24B tm63MiddleAfter24Head
    hn hbound
  have hrow' :
      run tm2
        (proposedIncrementCost 2
          (16*tm63RootResidueSixK-9)
          tm63MiddleAfter24A tm63MiddleAfter24B)
        (s1Config tm63Length1
          (16*tm63RootResidueSixK-9) 2
          tm63MiddleAfter24A 0 tm63MiddleAfter24B
          tm63MiddleAfter24Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-10) 1
        (tm63MiddleAfter24A+tm63MiddleAfter24B+2) 0
        (2^tm63MiddleAfter24B-1)
        (tm63MiddleAfter24Head+5+3*tm63MiddleAfter24B)) := by
    simpa [tm63MiddleAfter25A,tm63MiddleAfter25B,
      tm63MiddleAfter25Head] using hrow
  have hcomp := run_compose_local
    tm63_blank_reaches_after_middle24 hrow'
  simpa [tm63MiddleFirst25Moves,tm63MiddleAfter25A,
    tm63MiddleAfter25B,tm63MiddleAfter25Head] using hcomp

#print axioms tm63_blank_reaches_after_middle25

end BB6Coverage.Agent42TM63RootMiddle25
