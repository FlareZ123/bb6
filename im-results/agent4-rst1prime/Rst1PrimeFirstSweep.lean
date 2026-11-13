import CountedSweep
import CountedSuffixOutput
import S1Encoder
import Lean.Elab.Tactic.Omega

/-!
# First counted sweep precondition for Rst1'

For every genuine S1 input in the Rst1' family S1(L,0,1,a,0,b,h),
the first 3a+1 cells facing left from the head are ones, and the cell
immediately to the right of the head is zero.  Therefore the existing
original-machine counted_left_sweep theorem applies without any bounded
tape approximation.
-/

namespace BB6Coverage.Agent4Rst1Prime

open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent24ChampionTime

/-- Exact source-side preconditions for the first Rst1' counted sweep. -/
theorem rst1Prime_firstSweep_preconditions
    (L a b : Nat) (h : Int) :
    leftOnes (s1Config L 0 1 a 0 b h).tape h (3*a+1) ∧
    (s1Config L 0 1 a 0 b h).tape (h+1) = false := by
  constructor
  · intro i hi
    have hcell := s1Config_left_cell L 0 1 a 0 b h i
    rw [hcell]
    simp only [s1LeftFacing,binDec_zero]
    rw [sideBit_append]
    rw [d1pow_length]
    by_cases hi0 : i < 3*a
    · simp [hi0,sideBit_d1pow_true a i hi0]
    · have heq : i = 3*a := by omega
      subst i
      simp [markerWord]
  · have hcell := s1Config_right_cell L 0 1 a 0 b h 0
    simpa [s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hcell

/-- The first Rst1' phase is an exact 9a+3-transition original-machine
run, with the full infinite tape update retained. -/
theorem rst1Prime_firstSweep_run
    (L a b : Nat) (h : Int) :
    run tm2 (9*a+3) (s1Config L 0 1 a 0 b h) =
      some ⟨3,h-((3*a+1:Int)),
        sweptLeft (3*a+1) (s1Config L 0 1 a 0 b h).tape h⟩ := by
  obtain ⟨hleft,hright⟩ :=
    rst1Prime_firstSweep_preconditions L a b h
  have hrun := counted_left_sweep (3*a+1)
    (s1Config L 0 1 a 0 b h).tape h hleft hright
  have hcost : 3*(3*a+1)=9*a+3 := by omega
  simpa [s1Config,hcost] using hrun

#print axioms rst1Prime_firstSweep_preconditions
#print axioms rst1Prime_firstSweep_run

end BB6Coverage.Agent4Rst1Prime
