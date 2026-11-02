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

/-- The immediately preceding primitive configuration is F scanning 1. -/
def c65 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨false :: pairs (m+2) ++ [true,true], true,
     [true,true,true,false,true,false,true,false,true,false] ++ ys, 5⟩

theorem segment65 (m : Nat) (ys : List Bool) :
    run 5 (c60 m ys) = c65 m ys := by
  simp [c60,c65,run,step,goL,goR,pairs]

theorem e_zero_before_halt (m : Nat) (ys : List Bool) :
    run 65 (startE m ys) = c65 m ys := by
  have ht : 65=20+(20+(20+5)) := by omega
  rw [ht,run_add,segment20,run_add,segment40,run_add,segment60]
  exact segment65 m ys

theorem frozen_step (c : Cfg) (h : c.st = 6) : step c = c := by
  rcases c with ⟨l,b,r,st⟩
  change st=6 at h
  subst st
  cases b <;> rfl

theorem frozen_run (c : Cfg) (h : c.st = 6) (n : Nat) :
    run n c = c := by
  have hs := frozen_step c h
  induction n with
  | zero => rfl
  | succ n ih => simpa [run,hs] using ih

theorem e_zero_exact_first_halt (m : Nat) (ys : List Bool) (t : Nat)
    (ht : t < 66) : (run t (startE m ys)).st ≠ 6 := by
  intro hc
  have hh : 65=t+(65-t) := by omega
  have hg : (run 65 (startE m ys)).st=6 := by
    rw [hh,run_add]
    rw [frozen_run _ hc]
    exact hc
  rw [e_zero_before_halt] at hg
  simp [c65] at hg

/-- The authentic F-entry halting cylinder first enters state 6 exactly
    after the stated primitive time, and never at any smaller time. -/
theorem full_E_zero_halt_before (k : Nat) (ys : List Bool) :
    (run (12*k*k+41*k+98)
      (init (List.replicate (3*k+2) true ++
         false :: ([true,true,false,true,true,false,false] ++ ys)))).st = 5 := by
  have ht : 12*k*k+41*k+98 =
      (12*k*k+41*k+33)+65 := by omega
  rw [ht,run_add,prefix_E]
  change (run 65 (startE (4*k) ys)).st = 5
  rw [e_zero_before_halt]
  rfl

theorem full_E_zero_exact_first_halt (k : Nat) (ys : List Bool) (t : Nat)
    (ht : t < 12*k*k+41*k+99) :
    (run t
      (init (List.replicate (3*k+2) true ++
        false :: ([true,true,false,true,true,false,false] ++ ys)))).st ≠ 6 := by
  intro hc
  have heq : 12*k*k+41*k+98 =
      t + (12*k*k+41*k+98-t) := by omega
  have hh : (run (12*k*k+41*k+98)
      (init (List.replicate (3*k+2) true ++
        false :: ([true,true,false,true,true,false,false] ++ ys)))).st = 6 := by
    rw [heq,run_add]
    rw [frozen_run _ hc]
    exact hc
  rw [full_E_zero_halt_before] at hh
  omega

#print axioms e_zero_exact_first_halt
#print axioms full_E_zero_exact_first_halt
#print axioms segment20
#print axioms e_zero_halt
#print axioms full_E_zero_halt
end BB6.Agent32EZeroHalt
