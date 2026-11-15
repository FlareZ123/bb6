import TM63RootResidueZero
import M1OddResidueSeven
import Lean.Elab.Tactic.Omega

/-!
# Candidate authentic-root extension through middle row 17

After middle16, the source has m=1 and n=32*k+15. This is
n=8*q+7 with q=4*k+1, so the source-exact residue-seven transition applies.
The theorem composes that increment with the middle16 blank-root prefix.
-/

namespace BB6Coverage.Agent41TM63RootResidueSeven

open BB6ChampionArithmetic
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent41TM63RootResidueZero
open BB6Coverage.Agent41M1ResidueSeven

set_option maxHeartbeats 3000000

/-- The quotient for the n=8*q+7 row after middle16. -/
def tm63RootResidueSevenQ : Nat :=
  4*tm63RootResidueZeroK+1

private theorem tm63_root_residue7_bound :
    8*tm63RootResidueSevenQ+7 < 2^tm63Length1 := by
  have h := tm63_root_residue0_bound
  have hq :
      8*tm63RootResidueSevenQ+7 =
        32*tm63RootResidueZeroK+15 := by
    dsimp [tm63RootResidueSevenQ]
    omega
  rw [hq]
  omega

private theorem tm63_middle_after16_a_pos :
    0 < tm63MiddleAfter16A := by
  simp [tm63MiddleAfter16A]

/-- Endpoint after the m=1,n=32*k+15 counted increment. -/
def tm63MiddleAfter17A : Nat :=
  tm63MiddleAfter16A+tm63MiddleAfter16B+2

def tm63MiddleAfter17B : Nat :=
  2^tm63MiddleAfter16B-1

def tm63MiddleAfter17Head : Int :=
  tm63MiddleAfter16Head+5+3*tm63MiddleAfter16B

/-- Exact cumulative source-run length through the m=1,n=32*k+15 row. -/
def tm63MiddleFirst17Moves : Nat :=
  tm63MiddleFirst16Moves+
    proposedIncrementCost 1 (32*tm63RootResidueZeroK+15)
      tm63MiddleAfter16A tm63MiddleAfter16B

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add,h1]
  simp only [Option.bind_some]
  exact h2

/-- Candidate blank-root original-machine prefix through middle row 17. -/
theorem tm63_blank_reaches_after_middle17 :
    run tm2 tm63MiddleFirst17Moves blank =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-2) 0
        tm63MiddleAfter17A 0 tm63MiddleAfter17B
        tm63MiddleAfter17Head) := by
  have hsplit := tm63_root_residue6_split
  have hn :
      8*tm63RootResidueSevenQ+7 =
        32*tm63RootResidueZeroK+15 := by
    dsimp [tm63RootResidueSevenQ]
    omega
  have htarget :
      8*tm63RootResidueSevenQ+6 =
        32*tm63RootResidueZeroK+14 := by
    dsimp [tm63RootResidueSevenQ]
    omega
  have hinputRoot :
      32*tm63RootResidueZeroK+15 =
        16*tm63RootResidueSixK-1 := by omega
  have htargetRoot :
      32*tm63RootResidueZeroK+14 =
        16*tm63RootResidueSixK-2 := by omega
  have hL : 3 ≤ tm63Length1 := by
    have h5 := tm63_root_length_ge_five
    omega
  have hrow := m1ResidueSeven_counted_increment_source
    tm63Length1 tm63RootResidueSevenQ
    tm63MiddleAfter16A tm63MiddleAfter16B tm63MiddleAfter16Head
    hL tm63_root_residue7_bound tm63_middle_after16_a_pos
  have hrow' :
      run tm2
        (proposedIncrementCost 1
          (16*tm63RootResidueSixK-1)
          tm63MiddleAfter16A tm63MiddleAfter16B)
        (s1Config tm63Length1
          (16*tm63RootResidueSixK-1) 1
          tm63MiddleAfter16A 0 tm63MiddleAfter16B
          tm63MiddleAfter16Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-2) 0
        tm63MiddleAfter17A 0 tm63MiddleAfter17B
        tm63MiddleAfter17Head) := by
    simpa [hn,htarget,hinputRoot,htargetRoot,tm63MiddleAfter17A,
      tm63MiddleAfter17B,tm63MiddleAfter17Head] using hrow
  have hcomp := run_compose_local
    tm63_blank_reaches_after_middle16 hrow'
  simpa [tm63MiddleFirst17Moves] using hcomp

#print axioms tm63_root_residue7_bound
#print axioms tm63_blank_reaches_after_middle17

end BB6Coverage.Agent41TM63RootResidueSeven
