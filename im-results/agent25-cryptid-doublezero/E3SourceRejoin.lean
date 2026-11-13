import Lean.Elab.Tactic.Omega
import DRegularSourceShift
import EZeroZTwoA
import BoundaryPadding

namespace BB6.Agent25E3SourceBridge

open CryptidBoundary
open BB6.BoundaryPadding BB6.Padding

/-- The authentic regular-language E input. -/
def sourceStart (t : Nat) : Cfg :=
  DRegularSource.sourceSection ⟨9*t+4,1,1⟩

/-- Agent 36's prepared version carries two explicit far-right blanks. -/
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
    omega
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

/-- General regular-section representation for every q=1,b=1 E input. -/
def sourceStartK (k : Nat) : Cfg :=
  DRegularSource.sourceSection ⟨3*k+4,1,1⟩

def preparedStartK (k : Nat) : Cfg :=
  BB6.Agent36EZeroZTwoFollow.input k 0

theorem input_obs_eq_all (k : Nat) :
    ObsEq (sourceStartK k) (preparedStartK k) := by
  let xs : List Bool :=
    List.replicate (3*k+2) true ++ [false,true,true]
  have hpad : ObsEq (init xs) (init (xs ++ [false,false])) := by
    simpa [CryptidBoundary.run] using
      (BB6.BoundaryPadding.source_init_pad 0 2 xs)
  have hlen : 3*k+4-2 = 3*k+2 := by omega
  have hstart : sourceStartK k = init xs := by
    simp [sourceStartK, xs, DRegularSource.sourceSection,
      CryptidBoundary.init, CryptidBoundary.oppairs, hlen]
  have hprepared : preparedStartK k = init (xs ++ [false,false]) := by
    simp [preparedStartK, xs, BB6.Agent36EZeroZTwoFollow.input,
      CryptidBoundary.init, CryptidBoundary.pairs, List.append_assoc]
  rw [hstart, hprepared]
  exact hpad

def bDuration (t : Nat) : Nat :=
  BB6.Agent36EZeroZTwoFollow.firstTime (3*t+1) 0 +
    BB6.Agent36EZeroZTwoFollow.bTime t

def eDuration (t : Nat) : Nat :=
  BB6.Agent36EZeroZTwoFollow.firstTime (3*t+2) 0 +
    BB6.Agent36EZeroZTwoFollow.eTime t

def bOutput (t : Nat) : Cfg :=
  ⟨[],false,
    List.replicate (64*t+37) true ++ BB6.Agent36EZeroZTwoFollow.tail7,5⟩

def eOutput (t : Nat) : Cfg :=
  ⟨[],false,
    List.replicate (64*t+49) true ++ BB6.Agent36EZeroZTwoFollow.tail13,5⟩

private theorem two_ones_append (n : Nat) :
    [true,true] ++ List.replicate n true = List.replicate (n+2) true := by
  simp [List.replicate_succ]

/-- The B-return's one trailing zero is only the first blank beyond (01)^3. -/
private theorem b_output_obs_eq (t : Nat) :
    ObsEq (bOutput t) (DRegularSource.sourceSection ⟨64*t+37,3,0⟩) := by
  let xs : List Bool :=
    List.replicate (64*t+35) true ++ CryptidBoundary.oppairs 3
  have hpad : ObsEq (init xs) (init (xs ++ [false])) := by
    simpa [CryptidBoundary.run] using
      (BB6.BoundaryPadding.source_init_pad 0 1 xs)
  have hlen : 64*t+37-2 = 64*t+35 := by omega
  have htarget :
      DRegularSource.sourceSection ⟨64*t+37,3,0⟩ = init xs := by
    simp [DRegularSource.sourceSection, xs, CryptidBoundary.init,
      CryptidBoundary.oppairs, hlen]
  have hout : init (xs ++ [false]) = bOutput t := by
    change ⟨[],false,
      [true,true] ++ xs ++ [false],5⟩ = bOutput t
    rw [show [true,true] ++ List.replicate (64*t+35) true =
      List.replicate (64*t+37) true by
        simpa using two_ones_append (64*t+35)]
    simp [bOutput, xs, BB6.Agent36EZeroZTwoFollow.tail7,
      CryptidBoundary.oppairs, List.append_assoc]
  have hforward :
      ObsEq (DRegularSource.sourceSection ⟨64*t+37,3,0⟩) (bOutput t) := by
    rw [htarget, hout]
    exact hpad
  exact BB6.Padding.cfgEq_symm hforward

/-- The E-return's one trailing zero is only the first blank beyond (01)^6. -/
private theorem e_output_obs_eq (t : Nat) :
    ObsEq (eOutput t) (DRegularSource.sourceSection ⟨64*t+49,6,0⟩) := by
  let xs : List Bool :=
    List.replicate (64*t+47) true ++ CryptidBoundary.oppairs 6
  have hpad : ObsEq (init xs) (init (xs ++ [false])) := by
    simpa [CryptidBoundary.run] using
      (BB6.BoundaryPadding.source_init_pad 0 1 xs)
  have hlen : 64*t+49-2 = 64*t+47 := by omega
  have htarget :
      DRegularSource.sourceSection ⟨64*t+49,6,0⟩ = init xs := by
    simp [DRegularSource.sourceSection, xs, CryptidBoundary.init,
      CryptidBoundary.oppairs, hlen]
  have hout : init (xs ++ [false]) = eOutput t := by
    change ⟨[],false,
      [true,true] ++ xs ++ [false],5⟩ = eOutput t
    rw [show [true,true] ++ List.replicate (64*t+47) true =
      List.replicate (64*t+49) true by
        simpa using two_ones_append (64*t+47)]
    simp [eOutput, xs, BB6.Agent36EZeroZTwoFollow.tail13,
      CryptidBoundary.oppairs, List.append_assoc]
  have hforward :
      ObsEq (DRegularSource.sourceSection ⟨64*t+49,6,0⟩) (eOutput t) := by
    rw [htarget, hout]
    exact hpad
  exact BB6.Padding.cfgEq_symm hforward

theorem q1b1_regular_rejoin_B (t : Nat) :
    ObsEq
      (run (bDuration t) (sourceStartK (3*t+1)))
      (DRegularSource.sourceSection ⟨64*t+37,3,0⟩) := by
  have htransport := BB6.BoundaryPadding.source_congr
    (bDuration t) (input_obs_eq_all (3*t+1))
  have hraw :
      run (bDuration t) (preparedStartK (3*t+1)) = bOutput t := by
    simpa [bDuration, preparedStartK, bOutput] using
      (BB6.Agent36EZeroZTwoFollow.b_two_return t 0)
  have htail0 :
      ObsEq (run 0 (bOutput t))
        (run 0 (DRegularSource.sourceSection ⟨64*t+37,3,0⟩)) := by
    simpa [CryptidBoundary.run] using b_output_obs_eq t
  simpa [Nat.add_zero] using
    (BB6.BoundaryPadding.source_chain (bDuration t) 0
      (sourceStartK (3*t+1)) (bOutput t)
      (DRegularSource.sourceSection ⟨64*t+37,3,0⟩)
      (by simpa [hraw] using htransport) htail0)

theorem q1b1_regular_rejoin_E (t : Nat) :
    ObsEq
      (run (eDuration t) (sourceStartK (3*t+2)))
      (DRegularSource.sourceSection ⟨64*t+49,6,0⟩) := by
  have htransport := BB6.BoundaryPadding.source_congr
    (eDuration t) (input_obs_eq_all (3*t+2))
  have hraw :
      run (eDuration t) (preparedStartK (3*t+2)) = eOutput t := by
    simpa [eDuration, preparedStartK, eOutput] using
      (BB6.Agent36EZeroZTwoFollow.e_two_return t 0)
  have htail0 :
      ObsEq (run 0 (eOutput t))
        (run 0 (DRegularSource.sourceSection ⟨64*t+49,6,0⟩)) := by
    simpa [CryptidBoundary.run] using e_output_obs_eq t
  simpa [Nat.add_zero] using
    (BB6.BoundaryPadding.source_chain (eDuration t) 0
      (sourceStartK (3*t+2)) (eOutput t)
      (DRegularSource.sourceSection ⟨64*t+49,6,0⟩)
      (by simpa [hraw] using htransport) htail0)

/-- Every q=1,b=1 E section returns to the canonical D-regular language.
    The three residues of k use the existing A, B, and E source returns. -/
theorem q1b1_rejoins_regular (k : Nat) :
    ∃ n s, DRegular.Canon s ∧
      ObsEq (run n (sourceStartK k)) (DRegularSource.sourceSection s) := by
  by_cases h0 : k % 3 = 0
  · let t := k / 3
    have hk : k = 3*t := by omega
    subst k
    refine ⟨duration t, ⟨64*t+27,0,0⟩, ?_, ?_⟩
    · constructor
      · dsimp
        omega
      · right
        rfl
    · simpa [sourceStartK, sourceStart] using q1b1_regular_rejoin t
  · by_cases h1 : k % 3 = 1
    · let t := (k-1) / 3
      have hk : k = 3*t+1 := by omega
      subst k
      refine ⟨bDuration t, ⟨64*t+37,3,0⟩, ?_, q1b1_regular_rejoin_B t⟩
      constructor
      · dsimp
        omega
      · left
        omega
    · have h2 : k % 3 = 2 := by omega
      let t := (k-2) / 3
      have hk : k = 3*t+2 := by omega
      subst k
      refine ⟨eDuration t, ⟨64*t+49,6,0⟩, ?_, q1b1_regular_rejoin_E t⟩
      constructor
      · dsimp
        omega
      · left
        omega

#print axioms input_obs_eq
#print axioms q1b1_regular_rejoin
#print axioms q1b1_regular_rejoin_B
#print axioms q1b1_regular_rejoin_E
#print axioms q1b1_rejoins_regular

end BB6.Agent25E3SourceBridge
