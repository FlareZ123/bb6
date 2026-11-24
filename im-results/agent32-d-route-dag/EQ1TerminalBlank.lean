import Boundary
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.Agent32EQ1TerminalBlank
open CryptidBoundary

def startE (m : Nat) : Cfg :=
  ⟨[false,false] ++ pairs (m+3) ++ [true,true],false,
    [true,false,true,true,false,true,true],4⟩

def terminal (m : Nat) : Cfg :=
  ⟨false :: (pairs (m+1) ++ [true,true]),true,List.replicate 15 true,5⟩

/-- The final external halting-cylinder suffix, with the implicit blank
    tail, reaches the actual undefined F/1 cell after exactly 113 live steps. -/
theorem boundary_terminal (m : Nat) : run 113 (startE m) = terminal m := by
  simp [startE,terminal,run,step,goL,goR,pairs]

def start (k : Nat) : Cfg :=
  init (List.replicate (3*k+2) true ++ false ::
    [true,false,true,true,false,true,true])

def liveTime (k : Nat) : Nat := 12*k*k+41*k+146

theorem full_terminal (k : Nat) : run (liveTime k) (start k) = terminal (4*k) := by
  unfold liveTime start
  rw [show 12*k*k+41*k+146 = (12*k*k+41*k+33)+113 by omega,
    run_add,prefix_E]
  exact boundary_terminal (4*k)

theorem full_frozen (k : Nat) : (run (liveTime k+1) (start k)).st = 6 := by
  rw [run_add,full_terminal]
  rfl

private theorem frozen_step (c : Cfg) (h : c.st = 6) : step c = c := by
  rcases c with ⟨l,b,r,st⟩
  change st=6 at h
  subst st
  cases b <;> rfl

private theorem frozen_run (c : Cfg) (h : c.st = 6) (n : Nat) : run n c = c := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [run,frozen_step c h] using ih

/-- No earlier frozen-state entry is possible, by absorption and the
    live F/1 configuration at the stated exact time. -/
theorem full_first_frozen (k t : Nat) (ht : t < liveTime k+1) :
    (run t (start k)).st ≠ 6 := by
  intro h
  have he : liveTime k = t+(liveTime k-t) := by omega
  have hs : (run (liveTime k) (start k)).st = 6 := by
    rw [he,run_add,frozen_run _ h]
    exact h
  rw [full_terminal] at hs
  simp [terminal] at hs

#print axioms full_terminal
#print axioms full_frozen
#print axioms full_first_frozen
end BB6.Agent32EQ1TerminalBlank
