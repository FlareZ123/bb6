import Lean.Elab.Tactic.Omega
import Boundary

set_option maxHeartbeats 20000000
set_option maxRecDepth 2000
set_option linter.unusedSimpArgs false

namespace BB6.CryptidAHalt
open CryptidBoundary

/-- A fixed ten-bit right word causing halt, regardless of left tape
    and of all unknown right cells beyond the word. -/
def haltWord : List Bool :=
  [true,true,false,true,true,false,true,true,false,false]

/-- At step 68 the head is in the unhalted F-on-one state. -/
theorem a_before_halt (L ys : List Bool) :
    (run 68 (⟨L,false,haltWord ++ ys,0⟩ : Cfg)).st = 5 ∧
    (run 68 (⟨L,false,haltWord ++ ys,0⟩ : Cfg)).h = true := by
  constructor <;> simp [haltWord,run,step,goL,goR]

/-- The genuine original six-state machine enters frozen halt state6 at
    step 69 for arbitrary left and right tails. -/
theorem a_halt_69 (L ys : List Bool) :
    (run 69 (⟨L,false,haltWord ++ ys,0⟩ : Cfg)).st = 6 := by
  simp [haltWord,run,step,goL,goR]

/-- Complete exact eventual halt from a family of F-on-blank sections. -/
theorem full_A_halt (k : Nat) (ys : List Bool) :
    (run (12*k*k+41*k+101)
      (init (List.replicate (3*k+1) true ++
        false :: (haltWord ++ ys)))).st = 6 := by
  have ht : 12*k*k+41*k+101 = (12*k*k+41*k+32)+69 := by omega
  rw [ht,run_add,prefix_A]
  change (run 69
    (⟨false :: pairs (4*k+3) ++ [true,true], false,
      haltWord ++ ys,0⟩ : Cfg)).st = 6
  exact a_halt_69 _ _

#print axioms a_before_halt
#print axioms a_halt_69
#print axioms full_A_halt
end BB6.CryptidAHalt
