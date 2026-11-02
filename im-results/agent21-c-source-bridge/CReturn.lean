import CSection
import Lean.Elab.Tactic.Omega

namespace BB6.CReturn
open BB6.CReachBridge BB6.CSection

/-- The c=3 and c=1 drain closes a zero-c section. -/
theorem finish_c3 (a k : Nat) :
    runN 2 (some (a,k,3)) = some (a,k+3,0) := by
  simp [runN, stepC, BB6CLine.nextC]

/-- Exact 2-parameter middle-band return when the first counter is odd. -/
theorem middle_odd (m r s : Nat) (h : r+s=2*m+3) :
    runN (2*m+2*r+5) (some (2*m+3,m+r+3,0)) =
      some (2*s,2*r+5,0) := by
  have hfirst : runN (2*m+3) (some (2*m+3,m+r+3,0)) =
      some (4*m+6,2,2*r+3) := by
    exact section_short_odd m (m+r+3) (2*r+2) (by omega)
  have hsw : runN (2*r) (some (4*m+6,2,2*r+3)) =
      some (2*s,2*r+2,3) := by
    have ha : 4*m+6 = 2*s+2*r := by omega
    rw [ha]
    have hs := sweep (2*r) (2*s) 2 0
    simpa only [Nat.zero_add, show 2+2*r=2*r+2 by omega] using hs
  rw [show 2*m+2*r+5 = (2*m+3)+(2*r+2) by omega,
      runN_add (2*m+3) (2*r+2), hfirst]
  rw [show 2*r+2 = (2*r)+2 by omega, runN_add (2*r) 2, hsw]
  exact finish_c3 (2*s) (2*r+2)

/-- Exact 2-parameter middle-band return when the first counter is even. -/
theorem middle_even (m r s : Nat) (h : r+s=2*m+1) :
    runN (2*m+2*r+6) (some (2*m+2,m+r+2,0)) =
      some (2*s+1,2*r+5,0) := by
  have hfirst : runN (2*m+2) (some (2*m+2,m+r+2,0)) =
      some (4*m+5,0,2*r+5) := by
    exact section_short_even m (m+r+2) (2*r+1) (by omega)
  have hsw : runN (2*r+2) (some (4*m+5,0,2*r+5)) =
      some (2*s+1,2*r+2,3) := by
    have ha : 4*m+5 = (2*s+1)+(2*r+2) := by omega
    rw [ha]
    have hs := sweep (2*r+2) (2*s+1) 0 0
    simpa only [Nat.zero_add] using hs
  rw [show 2*m+2*r+6 = (2*m+2)+((2*r+2)+2) by omega,
      runN_add (2*m+2) ((2*r+2)+2), hfirst]
  rw [runN_add (2*r+2) 2, hsw]
  exact finish_c3 (2*s+1) (2*r+2)

#print axioms middle_odd
#print axioms middle_even
end BB6.CReturn
