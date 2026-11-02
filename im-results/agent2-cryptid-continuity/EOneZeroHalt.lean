import Lean.Elab.Tactic.Omega
import Boundary

set_option maxHeartbeats 10000000
set_option maxRecDepth 2000
set_option linter.unusedSimpArgs false

namespace BB6.Agent2EOne
open CryptidBoundary

/-!
Raw six-state D-start Cryptid, literal source transition model imported from
Agent 31's checksum-pinned Boundary. This cylinder requires the final zero
after 101101100. Without that zero, arbitrary tails are counterexamples.
-/
def startE1 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨false :: false :: pairs (m+3) ++ [true,true], false,
    [true,false,true,true,false,true,true,false,false] ++ ys, 4⟩

def c10 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[false,true,false,true,false,true,true,false] ++ pairs (m+2) ++ [true,true], false,
    [false,true,true,false,false] ++ ys, 2⟩

def c20 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[false,true,true,false,true,true,false,true,false,true,true,false] ++ pairs (m+2) ++ [true,true], false,
    [false] ++ ys, 0⟩

def c30 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[true,false,false,true,false,true,true,false] ++ pairs (m+2) ++ [true,true], true,
    [true,true,true,true,true] ++ ys, 1⟩

def c40 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[true,true,false,true,true,false] ++ pairs (m+2) ++ [true,true], true,
    [true,false,true,false,true,true,true] ++ ys, 1⟩

def c50 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[false,true,false,true,false,true,true,true,false,true,true,false] ++ pairs (m+2) ++ [true,true], true,
    [true] ++ ys, 0⟩

def c60 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[false,true,true,true,false,true,true,false] ++ pairs (m+2) ++ [true,true], false,
    [false,true,false,true,false] ++ ys, 1⟩

def c70 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[false,false] ++ pairs (m+2) ++ [true,true], false,
    [true,true,true,true,false,true,false,true,false,true,false] ++ ys, 0⟩

def c80 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[] ++ pairs (m+2) ++ [true,true], false,
    [true,true,false,true,false,true,false,true,false,true,false,true,false] ++ ys, 0⟩

def c90 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[true,false,true,false,true,true] ++ pairs (m+2) ++ [true,true], true,
    [false,true,false,true,false,true,false] ++ ys, 1⟩

def c100 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[true,false,true,false,true,false,true,false,true,false,true,true] ++ pairs (m+2) ++ [true,true], false,
    [true,true] ++ ys, 3⟩

def c110 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[true,true] ++ pairs (m+2) ++ [true,true], false,
    [true,true,true,true,true,true,true,true,true,true,true,true] ++ ys, 3⟩

theorem seg0 (m : Nat) (ys : List Bool) :
    run 10 (startE1 m ys) = c10 m ys := by
  simp [startE1,c10,run,step,goL,goR,pairs,List.append_assoc]

theorem seg10 (m : Nat) (ys : List Bool) :
    run 10 (c10 m ys) = c20 m ys := by
  simp [c10,c20,run,step,goL,goR,pairs,List.append_assoc]

theorem seg20 (m : Nat) (ys : List Bool) :
    run 10 (c20 m ys) = c30 m ys := by
  simp [c20,c30,run,step,goL,goR,pairs,List.append_assoc]

theorem seg30 (m : Nat) (ys : List Bool) :
    run 10 (c30 m ys) = c40 m ys := by
  simp [c30,c40,run,step,goL,goR,pairs,List.append_assoc]

theorem seg40 (m : Nat) (ys : List Bool) :
    run 10 (c40 m ys) = c50 m ys := by
  simp [c40,c50,run,step,goL,goR,pairs,List.append_assoc]

theorem seg50 (m : Nat) (ys : List Bool) :
    run 10 (c50 m ys) = c60 m ys := by
  simp [c50,c60,run,step,goL,goR,pairs,List.append_assoc]

theorem seg60 (m : Nat) (ys : List Bool) :
    run 10 (c60 m ys) = c70 m ys := by
  simp [c60,c70,run,step,goL,goR,pairs,List.append_assoc]

theorem seg70 (m : Nat) (ys : List Bool) :
    run 10 (c70 m ys) = c80 m ys := by
  simp [c70,c80,run,step,goL,goR,pairs,List.append_assoc]

theorem seg80 (m : Nat) (ys : List Bool) :
    run 10 (c80 m ys) = c90 m ys := by
  simp [c80,c90,run,step,goL,goR,pairs,List.append_assoc]

theorem seg90 (m : Nat) (ys : List Bool) :
    run 10 (c90 m (false :: ys)) = c100 m ys := by
  simp [c90,c100,run,step,goL,goR,pairs,List.append_assoc]

theorem seg100 (m : Nat) (ys : List Bool) :
    run 10 (c100 m ys) = c110 m ys := by
  simp [c100,c110,run,step,goL,goR,pairs,List.append_assoc]

theorem seg110 (m : Nat) (ys : List Bool) :
    (run 4 (c110 m ys)).st = 6 := by
  simp [c110,run,step,goL,goR,pairs,List.append_assoc]

/-- Guarded 114-step E halt, with a fully arbitrary tail after a mandatory zero. -/
theorem q1_to110 (m : Nat) (ys : List Bool) :
    run 110 (startE1 m (false :: ys)) = c110 m ys := by
  have ht0 : 110 = 10 + 100 := by omega
  rw [ht0,run_add,seg0]
  have ht1 : 100 = 10 + 90 := by omega
  rw [ht1,run_add,seg10]
  have ht2 : 90 = 10 + 80 := by omega
  rw [ht2,run_add,seg20]
  have ht3 : 80 = 10 + 70 := by omega
  rw [ht3,run_add,seg30]
  have ht4 : 70 = 10 + 60 := by omega
  rw [ht4,run_add,seg40]
  have ht5 : 60 = 10 + 50 := by omega
  rw [ht5,run_add,seg50]
  have ht6 : 50 = 10 + 40 := by omega
  rw [ht6,run_add,seg60]
  have ht7 : 40 = 10 + 30 := by omega
  rw [ht7,run_add,seg70]
  have ht8 : 30 = 10 + 20 := by omega
  rw [ht8,run_add,seg80]
  have ht9 : 20 = 10 + 10 := by omega
  rw [ht9,run_add,seg90]
  have ht10 : 10 = 10 + 0 := by omega
  rw [ht10,run_add,seg100]
  rfl

theorem q1_zero_halt (m : Nat) (ys : List Bool) :
    (run 114 (startE1 m (false :: ys))).st = 6 := by
  have ht : 114 = 110+4 := by omega
  rw [ht,run_add,q1_to110]
  exact seg110 m ys

theorem q1_zero_before_halt (m : Nat) (ys : List Bool) :
    (run 113 (startE1 m (false :: ys))).st = 5 := by
  have ht : 113 = 110+3 := by omega
  rw [ht,run_add,q1_to110]
  simp [c110,run,step,goL,goR,pairs]

/-- Every starting unary length 3k+4 and mandatory extra zero halts. -/
theorem full_E_one_zero_halt (k : Nat) (ys : List Bool) :
    (run (12*k*k+41*k+147)
      (init (List.replicate (3*k+2) true ++
        false :: ([true,false,true,true,false,true,true,false,false,false] ++ ys)))).st = 6 := by
  have ht : 12*k*k+41*k+147 = (12*k*k+41*k+33)+114 := by omega
  rw [ht,run_add,prefix_E]
  change (run 114 (startE1 (4*k) (false :: ys))).st = 6
  exact q1_zero_halt (4*k) ys

theorem full_E_one_zero_before (k : Nat) (ys : List Bool) :
    (run (12*k*k+41*k+146)
      (init (List.replicate (3*k+2) true ++
        false :: ([true,false,true,true,false,true,true,false,false,false] ++ ys)))).st = 5 := by
  have ht : 12*k*k+41*k+146 = (12*k*k+41*k+33)+113 := by omega
  rw [ht,run_add,prefix_E]
  change (run 113 (startE1 (4*k) (false :: ys))).st = 5
  exact q1_zero_before_halt (4*k) ys

theorem frozen_step (c : Cfg) (h : c.st=6) : step c=c := by
  rcases c with ⟨l,b,r,st⟩
  change st=6 at h
  subst st
  cases b <;> rfl

theorem frozen_run (c : Cfg) (h : c.st=6) (n : Nat) :
    run n c=c := by
  have hs := frozen_step c h
  induction n with
  | zero => rfl
  | succ n ih => simpa [run,hs] using ih

/-- Exact FIRST halt time for every member of the infinite original-source family. -/
theorem full_E_one_zero_first_halt (k : Nat) (ys : List Bool) (t : Nat)
    (ht : t < 12*k*k+41*k+147) :
    (run t
      (init (List.replicate (3*k+2) true ++
        false :: ([true,false,true,true,false,true,true,false,false,false] ++ ys)))).st ≠ 6 := by
  intro hc
  have heq : 12*k*k+41*k+146 =
      t + (12*k*k+41*k+146-t) := by omega
  have hh : (run (12*k*k+41*k+146)
      (init (List.replicate (3*k+2) true ++
        false :: ([true,false,true,true,false,true,true,false,false,false] ++ ys)))).st = 6 := by
    rw [heq,run_add]
    rw [frozen_run _ hc]
    exact hc
  rw [full_E_one_zero_before] at hh
  omega

#print axioms q1_to110
#print axioms q1_zero_halt
#print axioms full_E_one_zero_halt
#print axioms full_E_one_zero_before
#print axioms full_E_one_zero_first_halt

end BB6.Agent2EOne
