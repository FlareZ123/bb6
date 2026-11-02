import CFarReturn
import Lean.Elab.Tactic.Omega

namespace BB6.CGatewayTime
open BB6.CReachBridge BB6.CSection BB6.CReturn BB6.CFarReturn

/-- The even zero-first branch sends the critical high gate to c=2. -/
theorem critical_zero_branch (m : Nat) :
    stepC (some (0,4*m+8,5)) = some (8*m+18,2,2) := by
  have hp : (4*m+8)%2 = 0 := by omega
  have hd : (4*m+8)/2 = 2*m+4 := by omega
  change BB6CLine.nextC (0,4*m+8,5) = some (8*m+18,2,2)
  simp [BB6CLine.nextC,hp,hd]
  omega

/-- From every critical odd reset, the copied acceleration stops
    in exactly 6m+11 successful-or-failing calls. -/
theorem critical_stops (m : Nat) :
    runN (6*m+11) (some (2*m+3,3*m+7,0)) = none := by
  have hf : runN (2*m+3) (some (2*m+3,3*m+7,0)) =
      some (4*m+6,2,4*m+11) := by
    exact section_short_odd m (3*m+7) (4*m+10) (by omega)
  have hs : runN (4*m+6) (some (4*m+6,2,4*m+11)) =
      some (0,4*m+8,5) := by
    have hh := sweep (4*m+6) 0 2 2
    simpa only [Nat.zero_add, show 2+(4*m+6)+3=4*m+11 by omega,
        show 2+(4*m+6)=4*m+8 by omega, show 2+3=5 by omega] using hh
  rw [show 6*m+11=(2*m+3)+((4*m+6)+2) by omega,
      runN_add (2*m+3) ((4*m+6)+2),hf]
  rw [runN_add (4*m+6) 2,hs]
  change (stepC (stepC (some (0,4*m+8,5)))) = none
  rw [critical_zero_branch]
  rfl

#print axioms critical_stops
end BB6.CGatewayTime
