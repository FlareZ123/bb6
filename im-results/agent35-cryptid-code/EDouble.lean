import Lean.Elab.Tactic.Omega
import CryptidPairs

set_option maxHeartbeats 5000000
namespace BB6.Agent35
open CryptidBoundary

/-- Sixteen exact raw transitions for the A-on-1100 turn, leaving an
    arbitrary untouched left tail and an arbitrary right suffix. -/
theorem aFront16 (q : Nat) (L ys : List Bool) :
  run 16 (⟨oppairs (q+3) ++ L, false,
      [true,true,false,false] ++ ys, 0⟩ : Cfg) =
    cWalk (q+1) L ([true,false] ++ List.replicate 6 true ++ ys) := by
  simp [run, step, goL, goR, oppairs, cWalk]

/-- E right input (10)^(q+1)1100, with at least one initial pair. -/
def eDouble (m q : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs (m+2) ++ [true,true], false,
    pairs (q+1) ++ ([true,true,false,false] ++ ys), 4⟩

/-- Exactly 26 raw transitions for the base one-pair case. -/
theorem eDouble_base (m : Nat) (ys : List Bool) :
  run 26 (eDouble m 0 ys) =
    sweepB m (false :: List.replicate 4 true ++
      (false :: List.replicate 6 true ++ ys)) := by
  simp [eDouble, sweepB, run, step, goL, goR, pairs]

theorem eDouble_two (m q : Nat) (ys : List Bool) :
  run 2 (eDouble m q ys) =
  scanStart (q+2) (pairs (m+2) ++ [true,true])
    ([true,true,false,false] ++ ys) := by
  simp [eDouble, scanStart, run, step, goL, pairs]

/-- Four final moves after the variable-length opposite-pair reverse walk. -/
theorem cDouble_toB (m t : Nat) (ys : List Bool) :
  run 4 (⟨pairs (m+2) ++ [true,true], true,
      List.replicate t true ++ (false :: List.replicate 6 true ++ ys),2⟩ : Cfg) =
    sweepB m (false :: List.replicate (t+3) true ++
      (false :: List.replicate 6 true ++ ys)) := by
  simp [run, step, goL, pairs, sweepB]
  have h : List.replicate (t+3) true =
       [true,true,true] ++ List.replicate t true := by
    calc
      _ = List.replicate (3+t) true := by rw [Nat.add_comm]
      _ = List.replicate 3 true ++ List.replicate t true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  rw [h]
  rfl

/-- At least two right pairs: scan, fixed turn, reverse walk, close. -/
theorem eDouble_front_succ (m q : Nat) (ys : List Bool) :
    run (4*(q+2)+22) (eDouble m (q+1) ys) =
      sweepB m (false :: List.replicate (2*(q+2)+2) true ++
        (false :: List.replicate 6 true ++ ys)) := by
  have ht : 4*(q+2)+22 =
      (2+2*(q+3))+(16+(2*(q+1)+4)) := by omega
  rw [ht, run_add (2+2*(q+3)) (16+(2*(q+1)+4)),
      run_add 2 (2*(q+3)), eDouble_two, scan_run]
  change run (16+(2*(q+1)+4))
    (⟨oppairs (q+3) ++ (pairs (m+2) ++ [true,true]),false,
       [true,true,false,false] ++ ys,0⟩ : Cfg) = _
  rw [run_add 16 (2*(q+1)+4), aFront16]
  change run (2*(q+1)+4)
    (cWalk (q+1) (pairs (m+2) ++ [true,true])
       ([true,false] ++ List.replicate 6 true ++ ys)) = _
  rw [run_add (2*(q+1)) 4, cWalk_run]
  have hp : List.replicate (2*(q+1)) true ++
        ([true,false] ++ List.replicate 6 true ++ ys) =
      List.replicate (2*(q+1)+1) true ++
        (false :: List.replicate 6 true ++ ys) := by
    calc
      _ = (List.replicate (2*(q+1)) true ++ List.replicate 1 true) ++
          (false :: List.replicate 6 true ++ ys) := by
          simp [List.append_assoc]
      _ = _ := by rw [List.replicate_append_replicate]
  rw [hp, cDouble_toB]
  rw [show 2*(q+1)+1+3 = 2*(q+2)+2 by omega]

/-- Uniform E-to-B prefix for every count q+1 and any right suffix. -/
theorem eDouble_front (m q : Nat) (ys : List Bool) :
    run (4*(q+1)+22) (eDouble m q ys) =
      sweepB m (false :: List.replicate (2*(q+1)+2) true ++
        (false :: List.replicate 6 true ++ ys)) := by
  cases q with
  | zero => simpa using eDouble_base m ys
  | succ q => simpa using eDouble_front_succ m q ys

/-- Complete source-level E-on-(10)^(q+1)1100 return, all m,q,ys. -/
theorem eDouble_run (m q : Nat) (ys : List Bool) :
    run (2*m+4*(q+1)+25) (eDouble m q ys) =
      ⟨[],false,List.replicate (2*m+3) true ++
        (false :: List.replicate (2*(q+1)+2) true ++
          (false :: List.replicate 6 true ++ ys)),5⟩ := by
  have ht : 2*m+4*(q+1)+25 = (4*(q+1)+22)+(2*m+3) := by omega
  rw [ht, run_add, eDouble_front, sweepB_run]

/-- Original six-state F-to-F E return for all k,q and unknown suffix. -/
theorem full_E_double (k q : Nat) (ys : List Bool) :
    run (12*k*k+49*k+64+4*q)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs (q+1) ++ ([true,true,false,false] ++ ys)))) =
      ⟨[],false,List.replicate (8*k+5) true ++
        (false :: List.replicate (2*(q+1)+2) true ++
          (false :: List.replicate 6 true ++ ys)),5⟩ := by
  have ht : 12*k*k+49*k+64+4*q =
      (12*k*k+41*k+33)+(2*(4*k+1)+4*(q+1)+25) := by omega
  rw [ht, run_add, prefix_E]
  change run (2*(4*k+1)+4*(q+1)+25) (eDouble (4*k+1) q ys) = _
  rw [eDouble_run]
  rw [show 2*(4*k+1)+3=8*k+5 by omega]

#print axioms eDouble_front
#print axioms eDouble_run
#print axioms full_E_double
#print axioms eDouble_front_succ
#print axioms eDouble_two
#print axioms cDouble_toB
#print axioms eDouble_base
#print axioms aFront16
end BB6.Agent35
