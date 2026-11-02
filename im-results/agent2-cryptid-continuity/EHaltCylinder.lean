import Lean.Elab.Tactic.Omega
import Boundary

set_option maxHeartbeats 20000000
set_option maxRecDepth 2000
set_option linter.unusedSimpArgs false

namespace BB6.CryptidEHalt
open CryptidBoundary

def haltWord : List Bool :=
  [true,true,false,true,true,false,false]

/-- State E scanning zero, preceded by exactly 001 in the local left
    neighborhood, reaches F-on-one in 65 steps independent of all other tape. -/
theorem e_before_halt (L ys : List Bool) :
    (run 65 (⟨[false,false,true] ++ L,false,haltWord ++ ys,4⟩ : Cfg)).st = 5 ∧
    (run 65 (⟨[false,false,true] ++ L,false,haltWord ++ ys,4⟩ : Cfg)).h = true := by
  constructor <;> simp [haltWord,run,step,goL,goR]

/-- Universally halting E-boundary cylinder, fixed 66 primitive transitions. -/
theorem e_halt_66 (L ys : List Bool) :
    (run 66 (⟨[false,false,true] ++ L,false,haltWord ++ ys,4⟩ : Cfg)).st = 6 := by
  simp [haltWord,run,step,goL,goR]

/-- Original-machine F-on-zero E-class synthetic halting cylinder. -/
theorem full_E_halt (k : Nat) (ys : List Bool) :
    (run (12*k*k+41*k+99)
      (init (List.replicate (3*k+2) true ++
        false :: (haltWord ++ ys)))).st = 6 := by
  have ht : 12*k*k+41*k+99 = (12*k*k+41*k+33)+66 := by omega
  rw [ht,run_add,prefix_E]
  have hp : pairs (4*k+3) =
      true :: false :: pairs (4*k+2) := by
    rw [show 4*k+3 = (4*k+2)+1 by omega]
    rfl
  rw [hp]
  change (run 66
    (⟨[false,false,true] ++
        (false :: pairs (4*k+2) ++ [true,true]),false,
      haltWord ++ ys,4⟩ : Cfg)).st = 6
  exact e_halt_66 _ _

/-- Precisely one primitive step before every E-family halt,
    the source machine is F reading one. -/
theorem full_E_before_halt (k : Nat) (ys : List Bool) :
    (run (12*k*k+41*k+98)
      (init (List.replicate (3*k+2) true ++
        false :: (haltWord ++ ys)))).st = 5 ∧
    (run (12*k*k+41*k+98)
      (init (List.replicate (3*k+2) true ++
        false :: (haltWord ++ ys)))).h = true := by
  have ht : 12*k*k+41*k+98 = (12*k*k+41*k+33)+65 := by omega
  simp only [ht,run_add,prefix_E]
  have hp : pairs (4*k+3) =
      true :: false :: pairs (4*k+2) := by
    rw [show 4*k+3 = (4*k+2)+1 by omega]
    rfl
  rw [hp]
  exact e_before_halt _ _

#print axioms full_E_before_halt

#print axioms e_before_halt
#print axioms e_halt_66
#print axioms full_E_halt
end BB6.CryptidEHalt
