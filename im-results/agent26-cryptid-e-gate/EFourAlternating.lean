import Lean.Elab.Tactic.Omega
import CryptidSix

set_option maxHeartbeats 10000000
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false

namespace BB6.Agent26EFour

open CryptidBoundary

/-- A four-one E head followed by 0101010, with an arbitrary tail. -/
def fourWord : List Bool :=
  [true,true,true,true,false,true,false,true,false,true,false]

/-- Entire 13-bit packet after a 16-step E-to-B turn. -/
def sixPairsZero : List Bool :=
  [false,true,false,true,false,true,false,true,false,true,false,true,false]

def eFour (m : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs m ++ [true,true], false, fourWord ++ ys,4⟩

/-- This bounded turn does not inspect or change the remaining m pairs. -/
theorem eFour_front (m : Nat) (ys : List Bool) :
    run 16 (eFour m ys) = sweepB m (sixPairsZero ++ ys) := by
  simp [eFour, sweepB, fourWord, sixPairsZero,
    run, step, goL, goR, pairs, List.append_assoc]

theorem eFour_run (m : Nat) (ys : List Bool) :
    run (2*m+19) (eFour m ys) =
      ⟨[],false,List.replicate (2*m+3) true ++ (sixPairsZero ++ ys),5⟩ := by
  have ht : 2*m+19=16+(2*m+3) := by omega
  rw [ht,run_add,eFour_front,sweepB_run]

/-- Uniform full original-machine section for 0 11110101010 Y. -/
theorem full_E_four (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+58)
      (init (List.replicate (3*k+2) true ++
        false :: (fourWord ++ ys))) =
      ⟨[],false,List.replicate (8*k+9) true ++ (sixPairsZero ++ ys),5⟩ := by
  have ht : 12*k*k+49*k+58 =
      (12*k*k+41*k+33)+(2*(4*k+3)+19) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k+3)+19) (eFour (4*k+3) ys) = _
  rw [eFour_run]
  rw [show 2*(4*k+3)+3=8*k+9 by omega]

#print axioms eFour_front
#print axioms eFour_run
#print axioms full_E_four

end BB6.Agent26EFour
