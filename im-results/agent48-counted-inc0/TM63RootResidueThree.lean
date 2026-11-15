import TM63RootResidueTwo
import M0OddResidueOneSource
import Lean.Elab.Tactic.Omega

/-!
# Candidate authentic-root extension through middle row 15

This composes the candidate middle-14 endpoint with the m=0,n=8*k+1
source increment, instantiated at k=2*r.  The resulting candidate
middle-15 state has m=2 and n=16*r.

Status: source-level composition only; all imported candidate modules
still require original-import compilation and transitive axiom audits.
-/

namespace BB6Coverage.Agent48TM63RootResidueThree

open BB6ChampionArithmetic
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent8TM63RootResidueFour
open BB6Coverage.Agent48TM63RootResidueTwo
open BB6Coverage.Agent48M0OddResidueOneSource

set_option maxHeartbeats 3000000

private theorem eight_twice (r : Nat) : 8*(2*r)=16*r := by
  calc
    8*(2*r) = (8*2)*r := (Nat.mul_assoc 8 2 r).symm
    _ = 16*r := by rw [show 8*2=16 by decide]

private theorem tm63_root_residue1_bound :
    8*(2*tm63RootResidueSixK)+1 < 2^tm63Length1 := by
  have hroot := tm63_index1_lt_pow_length1
  have hmul := eight_twice tm63RootResidueSixK
  rw [hmul]
  rw [tm63_root_index_eq_16r15] at hroot
  omega

private theorem tm63_root_length_ge_three :
    3 ≤ tm63Length1 := by
  have h := tm63_root_length_ge_four
  omega

private theorem tm63_middle_after14_a_pos :
    0 < tm63MiddleAfter14A := by
  simp [tm63MiddleAfter14A]
  omega

/-- Endpoint after the m=0,n=16*r+1 marker-two increment. -/
def tm63MiddleAfter15A : Nat :=
  tm63MiddleAfter14A+tm63MiddleAfter14B+1

def tm63MiddleAfter15B : Nat :=
  2^tm63MiddleAfter14B-1

def tm63MiddleAfter15Head : Int :=
  tm63MiddleAfter14Head+5+3*tm63MiddleAfter14B

def tm63MiddleFirst15Moves : Nat :=
  tm63MiddleFirst14Moves+
    proposedIncrementCost 0 (16*tm63RootResidueSixK+1)
      tm63MiddleAfter14A tm63MiddleAfter14B

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add,h1]
  simp only [Option.bind_some]
  exact h2

/-- Candidate blank-root original-machine prefix through middle row 15.
The new row is the generalized m=0,n=8*k+1 source increment at k=2*r. -/
theorem tm63_blank_reaches_after_middle15 :
    run tm2 tm63MiddleFirst15Moves blank =
      some (s1Config tm63Length1 (16*tm63RootResidueSixK) 2
        tm63MiddleAfter15A 0 tm63MiddleAfter15B tm63MiddleAfter15Head) := by
  have hrow := m0Odd_residue1_counted_increment_source
    tm63Length1 (2*tm63RootResidueSixK)
    tm63MiddleAfter14A tm63MiddleAfter14B tm63MiddleAfter14Head
    tm63_root_length_ge_three tm63_root_residue1_bound
    tm63_middle_after14_a_pos
  have hrow' :
      run tm2
        (proposedIncrementCost 0 (16*tm63RootResidueSixK+1)
          tm63MiddleAfter14A tm63MiddleAfter14B)
        (s1Config tm63Length1 (16*tm63RootResidueSixK+1) 0
          tm63MiddleAfter14A 0 tm63MiddleAfter14B tm63MiddleAfter14Head) =
      some (s1Config tm63Length1 (16*tm63RootResidueSixK) 2
        tm63MiddleAfter15A 0 tm63MiddleAfter15B tm63MiddleAfter15Head) := by
    have hmul := eight_twice tm63RootResidueSixK
    simpa [tm63MiddleAfter15A,tm63MiddleAfter15B,tm63MiddleAfter15Head,
      hmul] using hrow
  exact run_compose_local tm63_blank_reaches_after_middle14 hrow'

#print axioms tm63_root_residue1_bound
#print axioms tm63_blank_reaches_after_middle15

end BB6Coverage.Agent48TM63RootResidueThree
