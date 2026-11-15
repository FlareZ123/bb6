import TM63RootResidueFour
import M1EvenResidueTwoSource
import Lean.Elab.Tactic.Omega

/-!
# Candidate authentic-root extension through middle row 14

This composes the current candidate blank-root endpoint after middle 13
with the generalized m=1, n=8k+2 counted increment.  The new source row
is instantiated at n=16*r+2, i.e. k=2*r.

Status: source-level composition only.  It depends on uncompiled row
modules and has not passed an original-import or transitive axiom audit.
-/

namespace BB6Coverage.Agent48TM63RootResidueTwo

open BB6ChampionArithmetic
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent8TM63RootResidueFour
open BB6Coverage.Agent48M1EvenResidueTwoSource

set_option maxHeartbeats 3000000

private theorem eight_twice (r : Nat) : 8*(2*r)=16*r := by
  calc
    8*(2*r) = (8*2)*r := (Nat.mul_assoc 8 2 r).symm
    _ = 16*r := by rw [show 8*2=16 by decide]

private theorem tm63_root_residue2_bound :
    8*(2*tm63RootResidueSixK)+2 < 2^tm63Length1 := by
  have hroot := tm63_index1_lt_pow_length1
  have hmul := eight_twice tm63RootResidueSixK
  rw [hmul]
  rw [tm63_root_index_eq_16r15] at hroot
  omega

private theorem tm63_root_length_ge_three :
    3 ≤ tm63Length1 := by
  have h := tm63_root_length_ge_four
  omega

private theorem tm63_middle_after13_a_pos :
    0 < tm63MiddleAfter13A := by
  simp [tm63MiddleAfter13A,nextExponent]

/-- Endpoint after the n=16*r+2, m=1 row. -/
def tm63MiddleAfter14A : Nat :=
  tm63MiddleAfter13A+tm63MiddleAfter13B+2

def tm63MiddleAfter14B : Nat :=
  2^tm63MiddleAfter13B-1

def tm63MiddleAfter14Head : Int :=
  tm63MiddleAfter13Head+5+3*tm63MiddleAfter13B

def tm63MiddleFirst14Moves : Nat :=
  tm63MiddleFirst13Moves+
    proposedIncrementCost 1 (16*tm63RootResidueSixK+2)
      tm63MiddleAfter13A tm63MiddleAfter13B

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add,h1]
  simp only [Option.bind_some]
  exact h2

/-- Candidate blank-root original-machine prefix through middle row 14.
The only new row is the generalized m=1, n=8k+2 counted source theorem,
instantiated at k=2*tm63RootResidueSixK. -/
theorem tm63_blank_reaches_after_middle14 :
    run tm2 tm63MiddleFirst14Moves blank =
      some (s1Config tm63Length1 (16*tm63RootResidueSixK+1) 0
        tm63MiddleAfter14A 0 tm63MiddleAfter14B tm63MiddleAfter14Head) := by
  have hrow := m1Even_residue2_counted_increment_source
    tm63Length1 (2*tm63RootResidueSixK)
    tm63MiddleAfter13A tm63MiddleAfter13B tm63MiddleAfter13Head
    tm63_root_length_ge_three tm63_root_residue2_bound
    tm63_middle_after13_a_pos
  have hrow' :
      run tm2
        (proposedIncrementCost 1 (16*tm63RootResidueSixK+2)
          tm63MiddleAfter13A tm63MiddleAfter13B)
        (s1Config tm63Length1 (16*tm63RootResidueSixK+2) 1
          tm63MiddleAfter13A 0 tm63MiddleAfter13B tm63MiddleAfter13Head) =
      some (s1Config tm63Length1 (16*tm63RootResidueSixK+1) 0
        tm63MiddleAfter14A 0 tm63MiddleAfter14B tm63MiddleAfter14Head) := by
    have hmul := eight_twice tm63RootResidueSixK
    simpa [tm63MiddleAfter14A,tm63MiddleAfter14B,tm63MiddleAfter14Head,
      hmul] using hrow
  exact run_compose_local tm63_blank_reaches_after_middle13 hrow'

#print axioms tm63_root_residue2_bound
#print axioms tm63_blank_reaches_after_middle14

end BB6Coverage.Agent48TM63RootResidueTwo
