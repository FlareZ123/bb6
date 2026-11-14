import CountedSweep
import CountedSuffixOutput
import CountedQ4Prefix
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
open BB6Coverage.Agent6Q4Prefix

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
    have hprefixLen :
        i < (d1pow a ++ markerWord 1 ++ d0 ++ d1pow L).length := by
      simp [List.length_append, d1pow_length, markerWord, d0]
      omega
    rw [if_pos hprefixLen]
    by_cases hi0 : i < 3*a
    · have hbit := sideBit_append_left (d1pow a)
        (markerWord 1 ++ d0 ++ d1pow L) i
        (by simpa [d1pow_length] using hi0)
      calc
        sideBit (d1pow a ++ markerWord 1 ++ d0 ++ d1pow L) i
            = sideBit (d1pow a ++ (markerWord 1 ++ d0 ++ d1pow L)) i := by
                simp only [List.append_assoc]
        _ = sideBit (d1pow a) i := hbit
        _ = true := BB6Coverage.Agent24ChampionTime.sideBit_d1pow_true a i hi0
    · have heq : i = 3*a := by omega
      subst i
      have hbit := sideBit_append_right (d1pow a)
        (markerWord 1 ++ d0 ++ d1pow L) (3*a)
        (by simp [d1pow_length])
      calc
        sideBit (d1pow a ++ markerWord 1 ++ d0 ++ d1pow L) (3*a)
            = sideBit (d1pow a ++ (markerWord 1 ++ d0 ++ d1pow L)) (3*a) := by
                simp only [List.append_assoc]
        _ = sideBit (markerWord 1 ++ d0 ++ d1pow L)
              (3*a - (d1pow a).length) := hbit
        _ = true := by simp [d1pow_length, markerWord, sideBit]
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
  simpa [s1Config, s0Config, hcost] using hrun

#print axioms rst1Prime_firstSweep_preconditions
#print axioms rst1Prime_firstSweep_run

end BB6Coverage.Agent4Rst1Prime
