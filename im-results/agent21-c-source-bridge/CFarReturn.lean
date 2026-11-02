import CReturn
import Lean.Elab.Tactic.Omega

namespace BB6.CFarReturn
open BB6.CReachBridge BB6.CSection BB6.CReturn

/-- Zero-first, odd-middle branch after a high sweep. -/
theorem odd_zero_branch (m t : Nat) :
    stepC (some (0,4*m+5,2*t+4)) = some (8*m+13,0,2*t+4) := by
  have hp : (4*m+5)%2 ≠ 0 := by omega
  have hd : (4*m+5)/2 = 2*m+2 := by omega
  change BB6CLine.nextC (0,4*m+5,2*t+4)=some (8*m+13,0,2*t+4)
  simp [BB6CLine.nextC, hp, hd]
  omega

/-- Zero-first, even-middle branch after a high sweep. -/
theorem even_zero_branch (m t : Nat) :
    stepC (some (0,4*m+8,2*t+7)) = some (8*m+18,2,2*t+4) := by
  have hp : (4*m+8)%2 = 0 := by omega
  have hd : (4*m+8)/2 = 2*m+4 := by omega
  change BB6CLine.nextC (0,4*m+8,2*t+7)=some (8*m+18,2,2*t+4)
  have hc : 2*t+7=(2*t+3)+4 := by omega
  rw [hc]
  simp [BB6CLine.nextC,hp,hd]
  omega

/-- Next c=0 return in the third (far-even) affine band. -/
theorem far_even (m t s : Nat) (h : t+s=4*m+6) :
    runN (6*m+2*t+11) (some (2*m+2,3*m+t+4,0)) =
      some (2*s,2*t+4,0) := by
  have hfirst : runN (2*m+2) (some (2*m+2,3*m+t+4,0)) =
      some (4*m+5,0,4*m+2*t+9) := by
    exact section_short_even m (3*m+t+4) (4*m+2*t+5) (by omega)
  have hs1 : runN (4*m+5) (some (4*m+5,0,4*m+2*t+9)) =
      some (0,4*m+5,2*t+4) := by
    have hs := sweep (4*m+5) 0 0 (2*t+1)
    simpa only [Nat.zero_add, show (2*t+1)+(4*m+5)+3=4*m+2*t+9 by omega] using hs
  have hs2 : runN (2*t+1) (some (8*m+13,0,2*t+4)) =
      some (2*s,2*t+1,3) := by
    have he : 8*m+13=2*s+(2*t+1) := by omega
    rw [he]
    simpa only [Nat.zero_add] using sweep (2*t+1) (2*s) 0 0
  rw [show 6*m+2*t+11=(2*m+2)+((4*m+5)+(1+((2*t+1)+2))) by omega,
      runN_add (2*m+2) ((4*m+5)+(1+((2*t+1)+2))), hfirst]
  rw [runN_add (4*m+5) (1+((2*t+1)+2)), hs1]
  rw [runN_add 1 ((2*t+1)+2)]
  change runN ((2*t+1)+2) (stepC (some (0,4*m+5,2*t+4))) = _
  rw [odd_zero_branch, runN_add (2*t+1) 2, hs2]
  exact finish_c3 (2*s) (2*t+1)

/-- Next c=0 return in the third (far-odd, noncritical) affine band. -/
theorem far_odd (m t s : Nat) (h : t+s=4*m+8) :
    runN (6*m+2*t+13) (some (2*m+3,3*m+t+8,0)) =
      some (2*s+1,2*t+6,0) := by
  have hfirst : runN (2*m+3) (some (2*m+3,3*m+t+8,0)) =
      some (4*m+6,2,4*m+2*t+13) := by
    exact section_short_odd m (3*m+t+8) (4*m+2*t+12) (by omega)
  have hs1 : runN (4*m+6) (some (4*m+6,2,4*m+2*t+13)) =
      some (0,4*m+8,2*t+7) := by
    have hs := sweep (4*m+6) 0 2 (2*t+4)
    simpa only [Nat.zero_add, show (2*t+4)+(4*m+6)+3=4*m+2*t+13 by omega,
        show 2+(4*m+6)=4*m+8 by omega,
        show (2*t+4)+3=2*t+7 by omega] using hs
  have hs2 : runN (2*t+1) (some (8*m+18,2,2*t+4)) =
      some (2*s+1,2*t+3,3) := by
    have he : 8*m+18=(2*s+1)+(2*t+1) := by omega
    rw [he]
    simpa only [Nat.zero_add, show (2*t+1)+3=2*t+4 by omega,
        show 2+(2*t+1)=2*t+3 by omega] using sweep (2*t+1) (2*s+1) 2 0
  rw [show 6*m+2*t+13=(2*m+3)+((4*m+6)+(1+((2*t+1)+2))) by omega,
      runN_add (2*m+3) ((4*m+6)+(1+((2*t+1)+2))), hfirst]
  rw [runN_add (4*m+6) (1+((2*t+1)+2)), hs1]
  rw [runN_add 1 ((2*t+1)+2)]
  change runN ((2*t+1)+2) (stepC (some (0,4*m+8,2*t+7))) = _
  rw [even_zero_branch, runN_add (2*t+1) 2, hs2]
  exact finish_c3 (2*s+1) (2*t+3)

#print axioms far_even
#print axioms far_odd
end BB6.CFarReturn
