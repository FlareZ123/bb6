import Lean.Elab.Tactic.Omega
import DRegularSourceShift
import EZeroZTwoA
import BoundaryPadding

namespace BB6.Agent25E3SourceBridge

open CryptidBoundary
open BB6.BoundaryPadding BB6.Padding

/-- The genuine regular-language representation of the q=1,b=1 E input. -/
def sourceStart (t : Nat) : Cfg :=
  DRegularSource.sourceSection ⟨9*t+4,1,1⟩

/-- Agent 36's prepared version carries two explicit far-right blank cells. -/
def preparedStart (t : Nat) : Cfg :=
  BB6.Agent36EZeroZTwoFollow.input (3*t) 0

def sourceEnd (t : Nat) : Cfg :=
  DRegularSource.sourceSection ⟨64*t+27,0,0⟩

def duration (t : Nat) : Nat :=
  BB6.Agent36EZeroZTwoFollow.firstTime (3*t) 0 +
    BB6.Agent36EZeroZTwoA.aTime t 0

/-- The two representations differ only by two explicit far-right zeros. -/
theorem input_obs_eq (t : Nat) :
    ObsEq (sourceStart t) (preparedStart t) := by
  let xs : List Bool :=
    List.replicate (9*t+2) true ++ [false,true,true]
  have hpad : ObsEq (init xs) (init (xs ++ [false,false])) := by
    simpa [CryptidBoundary.run] using
      (BB6.BoundaryPadding.source_init_pad 0 2 xs)
  have hstart : sourceStart t = init xs := by
    simp [sourceStart, xs, DRegularSource.sourceSection,
      CryptidBoundary.init, CryptidBoundary.oppairs]
  have hprepared : preparedStart t = init (xs ++ [false,false]) := by
    simp [preparedStart, xs, BB6.Agent36EZeroZTwoFollow.input,
      CryptidBoundary.init, CryptidBoundary.pairs, List.append_assoc]
  rw [hstart, hprepared]
  exact hpad

private theorem unary_sourceSection (n : Nat) :
    (⟨[],false,List.replicate (n+2) true,5⟩ : Cfg) =
      DRegularSource.sourceSection ⟨n+2,0,0⟩ := by
  simp [DRegularSource.sourceSection, CryptidBoundary.init,
    CryptidBoundary.oppairs, List.replicate_succ]

/-- The authentic L(9t+4,1,1) section returns to pure-unary L(64t+27).
    This composes Agent 36's E-zero/A-code source theorem with the exact
    two-blank physical-tape bridge above. -/
theorem q1b1_regular_rejoin (t : Nat) :
    ObsEq (run (duration t) (sourceStart t)) (sourceEnd t) := by
  have htransport := BB6.BoundaryPadding.source_congr
    (duration t) (input_obs_eq t)
  have hraw :
      run (duration t) (preparedStart t) =
        (⟨[],false,
          List.replicate (BB6.Agent36EZeroZTwoA.aUnary t 0) true,5⟩ : Cfg) := by
    simpa [duration, preparedStart] using
      (BB6.Agent36EZeroZTwoA.a_two_return_multiple_three t 0)
  have hval :
      BB6.Agent36EZeroZTwoA.aUnary t 0 = 64*t+27 := by
    simp [BB6.Agent36EZeroZTwoA.aUnary,
      BB6.Agent36EZeroZTwoA.aWords, CryptidA.wordInc]
    omega
  have hend :
      (⟨[],false,
        List.replicate (BB6.Agent36EZeroZTwoA.aUnary t 0) true,5⟩ : Cfg) =
        sourceEnd t := by
    rw [hval]
    simpa [sourceEnd] using unary_sourceSection (64*t+25)
  rw [hraw, hend] at htransport
  exact htransport

#print axioms input_obs_eq
#print axioms q1b1_regular_rejoin

end BB6.Agent25E3SourceBridge

-- CI retry: EZeroZTwoA's redundant closed-goal tactics were removed upstream.
