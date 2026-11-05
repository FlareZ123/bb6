import Agent6Pump
import BB429Rank
import BB429Burst
import Lean.Elab.Tactic.Omega

namespace Agent6Pump15
set_option maxHeartbeats 10000000

private theorem prefix15 (j : Nat) :
  BB429Burst.firstRun 15 (11,1048722+76*j)=some (458749,131291+76*j) := by
  have hg : 4*((11+3)*2^14) ≤ 2*11+(1048722+76*j)+3*14+9 := by omega
  obtain ⟨a,b,hfirst⟩ :=
    (BB429Burst.prefix_exists_iff 11 (1048722+76*j) 14).mpr hg
  have hp := BB429Burst.prefix_formula 11 (1048722+76*j) 15 a b (by simpa using hfirst)
  have ha : a=458749 := by omega
  have hb : b=131291+76*j := by omega
  simpa [ha,hb] using hfirst

/-- Every j<=2296 receives exactly 17 successful authentic macro steps,
returning to u=11 with second counter increased by 76. -/
theorem one_cycle (j : Nat) (hj : j≤2296) :
  BB429.run 17 (11,1048722+76*j)=some (11,1048722+76*(j+1)) := by
  have hb : 3≤131291+76*j := by omega
  have hodd : (131291+76*j)%2=1 := by omega
  have hd : 458749-(131291+76*j)/2=393104-38*j := by omega
  have h4 : 4≤458749-(131291+76*j)/2 := by omega
  have heven : (458749-(131291+76*j)/2)%2=0 := by omega
  have hexit : 131291+76*j ≤ (458749-(131291+76*j)/2)+7 := by omega
  have hp := Agent6Pump.pump 15 (1048722+76*j) 458749 (131291+76*j)
     (prefix15 j) hb hodd h4 heven hexit
  simpa [show 15+2=17 by decide, Nat.mul_add, Nat.add_assoc] using hp

/-- 2297 genuine consecutive 17-step affine cycles, compressed into one
all-natural induction instead of 39049 individual transition evaluations. -/
theorem run_cycles_2297 (j : Nat) (hj : j≤2297) :
  BB429.run (17*j) (11,1048722)=some (11,1048722+76*j) := by
  induction j with
  | zero => simp [BB429.run]
  | succ j ih =>
      have hprev := ih (by omega)
      rw [show 17*(j+1)=17*j+17 by omega, BB429.run_add, hprev]
      simp [one_cycle j (by omega)]

#print axioms one_cycle
#print axioms run_cycles_2297
end Agent6Pump15
