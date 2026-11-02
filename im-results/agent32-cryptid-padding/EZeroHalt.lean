import Lean.Elab.Tactic.Omega
import Boundary

set_option maxHeartbeats 5000000
set_option maxRecDepth 1024

namespace BB6.Agent32EZeroHalt

open CryptidBoundary

def startE (m : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs (m+3) ++ [true,true], false,
    [true,true,false,true,true,false,false] ++ ys, 4⟩

def c20 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[false,true,true,false,true,true,false,true] ++ pairs (m+3) ++ [true,true],
    true, [true] ++ ys, 2⟩

def c40 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[false,false,true,true] ++ pairs (m+3) ++ [true,true],
    false, [true,false,true,true,true] ++ ys, 4⟩

def c60 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[true,true] ++ pairs (m+3) ++ [true,true],
    true, [true,true,false,true,false,true,false] ++ ys, 0⟩

theorem segment20 (m : Nat) (ys : List Bool) :
    run 20 (startE m ys) = c20 m ys := by
  simp [startE,c20,run,step,goL,goR,pairs]

theorem segment40 (m : Nat) (ys : List Bool) :
    run 20 (c20 m ys) = c40 m ys := by
  simp [c20,c40,run,step,goL,goR,pairs]

theorem segment60 (m : Nat) (ys : List Bool) :
    run 20 (c40 m ys) = c60 m ys := by
  simp [c40,c60,run,step,goL,goR,pairs]

theorem segment66 (m : Nat) (ys : List Bool) :
    (run 6 (c60 m ys)).st = 6 := by
  simp [c60,run,step,goL,goR,pairs]

/-- An E section with prefix 1101100 reaches frozen halt state 6
    in exactly 66 further raw steps; the suffix is unrestricted. -/
theorem e_zero_halt (m : Nat) (ys : List Bool) :
    (run 66 (startE m ys)).st = 6 := by
  have htime : 66=20+(20+(20+6)) := by omega
  rw [htime,run_add,segment20,run_add,segment40,run_add,segment60]
  exact segment66 m ys

/-- An infinite family of genuine D-start six-state machine halting starts,
    one for every k and arbitrary unknown tape beyond the 01101100 prefix. -/
theorem full_E_zero_halt (k : Nat) (ys : List Bool) :
    (run (12*k*k+41*k+99)
      (init (List.replicate (3*k+2) true ++
         false :: ([true,true,false,true,true,false,false] ++ ys)))).st = 6 := by
  have ht : 12*k*k+41*k+99 = (12*k*k+41*k+33)+66 := by omega
  rw [ht,run_add,prefix_E]
  change (run 66 (startE (4*k) ys)).st = 6
  exact e_zero_halt (4*k) ys

#print axioms segment20
#print axioms e_zero_halt
#print axioms full_E_zero_halt
end BB6.Agent32EZeroHalt
