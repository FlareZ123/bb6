import Boundary
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 4096
set_option maxHeartbeats 25000000

namespace BB6.Agent31QuickHalt
open CryptidBoundary

/-- The original six-state machine halts in precisely 66 attempted primitive
    transitions from this E/0 boundary configuration, for *any* left remainder
    and any right suffix. The boundary scans at most three left cells and
    seven right cells before the undefined F/1 transition. -/
theorem e66 (left tail : List Bool) :
    (run 66
      (⟨false :: false :: true :: left, false,
        [true,true,false,true,true,false,false] ++ tail, 4⟩ : Cfg)).st = 6 := by
  simp [run, step, goR, goL]

private theorem left_pref (m : Nat) :
    false :: false :: pairs (m+3) ++ [true,true] =
    false :: false :: true :: (false :: pairs (m+2) ++ [true,true]) := by
  simp [pairs]

/-- Additional quantified actual-source D-machine halting cylinder.
    The finite right prefix, including both final zeros, is mandatory;
    any further arbitrary Boolean suffix is permitted. -/
theorem full_E_01101100_halt (k : Nat) (ys : List Bool) :
    (run (12*k*k+41*k+99)
      (init (List.replicate (3*k+2) true ++
        false :: ([true,true,false,true,true,false,false] ++ ys)))).st = 6 := by
  have ht : 12*k*k+41*k+99 = (12*k*k+41*k+33)+66 := by omega
  rw [ht, run_add, prefix_E]
  rw [left_pref (4*k)]
  exact e66 _ _

#print axioms e66
#print axioms full_E_01101100_halt
end BB6.Agent31QuickHalt
