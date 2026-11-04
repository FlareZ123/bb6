import EvenRightUnique
import ReachAffine
import OddOddLowVal
import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15
open BB6.Agent46

/-- An infinite genuine-blank unreachable Machine C return cylinder.
    For every u>=1, the exact R/A/O forced predecessors lead from
    (1,64u+10) to (56u+4,36u+1), where the original odd-right
    section-image invariant forbids total sum residue one mod four. -/
theorem blank_no_one_64u10 (u time : Nat) (hu : 1≤u) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (1,64*u+10) := by
  intro h
  have hR := blank_reach_iff_even_right 1 (64*u+10)
    (by omega) (by omega) (by omega) (by omega)
  have hR1 : 1+(64*u+10)-2=64*u+9 := by omega
  have hR2 : ((64*u+10-2)/2)=32*u+4 := by omega
  rw [hR1,hR2] at hR
  obtain ⟨n,hn⟩ := hR.mp ⟨time,h⟩
  have hA := blank_reach_iff_affine (64*u+9) (32*u+4)
    (by omega) (by omega) (by omega)
  have hA1 : 64*u+9+(32*u+4)-2=96*u+11 := by omega
  have hA2 : ((32*u+4-2)/2)=16*u+1 := by omega
  rw [hA1,hA2] at hA
  obtain ⟨s,hs⟩ := hA.mp ⟨n,hn⟩
  have hO := BB6.Agent3.oddodd_lowval_blank_reach_iff
    (96*u+11) (16*u+1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hO1 : ((96*u+11+(16*u+1)-4)/2)=56*u+4 := by omega
  have hO2 : ((96*u+11+3*(16*u+1)-10)/4)=36*u+1 := by omega
  rw [hO1,hO2] at hO
  obtain ⟨z,hz⟩ := hO.mp ⟨s,hs⟩
  cases z with
  | zero =>
      simp [BB6.Agent8Section.run] at hz
      omega
  | succ z =>
      have hi := BB6.Agent3.blank_section_odd_image z
        (56*u+4) (36*u+1) hz (by omega) (by omega)
      omega

#print axioms blank_no_one_64u10
end BB6.Agent15
